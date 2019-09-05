import os, subprocess, multiprocessing, sys
from pycparser import c_parser, c_ast, parse_file, plyparser
import re
from functools import reduce
from enum import Enum
from os import path
import tempfile

######################## utilities #############################################
def comment_remover(text):
    def replacer(match):
        s = match.group(0)
        if s.startswith('/'):
            return " " # note: a space and not an empty string
        else:
            return s
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE
    )
    return re.sub(pattern, replacer, text)


def rules_str(rls, indent = 0):
  ind = reduce(lambda s, _: s + " ", range(indent), "")
  if len(rls) == 0:
    return ""
  else:
    return reduce(lambda s, a: s + "\n" + ind + str(a), rls, "")[1:]

def concat(types):
    return reduce(lambda s, a: s + " " + a, types, "")[1:]

######################## terms #################################################
class Type:
  VOID = 0
  BOOL = 1
  INT = 2

  typename2spec = {
    "void"           : (VOID, 0, False),
    "bool"           : (BOOL, 1, False),
    "byte"           : (INT, 8, True),
    "short"          : (INT, 16, True),
    "int"            : (INT, 32, True),
    "long"           : (INT, 32, True),
    "unsigned byte"  : (INT, 8, False),
    "unsigned short" : (INT, 16, False),
    "unsigned"       : (INT, 32, False),
    "unsigned int"   : (INT, 32, False),
    "unsigned long"  : (INT, 32, False)
  }

  def __init__(self, t, b, is_signed):
    self.type = t
    self.bits = b
    self.is_signed = is_signed

  @classmethod
  def of_name(cls, str):
    kind, bits, is_signed = cls.typename2spec[str]
    return cls(kind, bits, is_signed)

  @classmethod
  def mkVoid(cls):
    return cls(cls.VOID, 0, False)

  @classmethod
  def mkBool(cls):
    return cls(cls.BOOL, 1, False)

  def __str__(self):
    if self.type == self.VOID:
      return "void"
    elif self.type == self.BOOL:
      return "bool"
    elif self.type == self.INT:
      return "int(" + str(self.bits) + ")"
    else:
      return "?"

  def __eq__(self, other):
    return self.type == other.type and self.bits == other.bits

  def isBool(self):
    return self.type == self.BOOL

  def isInteger(self):
    return self.type == self.INT

class Term:
  def __str__(self):
    pass

class Var(Term):
  def __init__(self, name, type):
    self.name = name
    self.type = type

  def __str__(self):
    return self.name

  def ctrl(self, var_map):
    return var_map[self.name] if self.name in var_map else self.name
  
  def symbols(self):
    return []
  
  def variables(self):
    return [self]

  def __eq__(self, other):
    return isinstance(other,Var) and self.name == other.name

class Fun(Term):
  def __init__(self, fname, type, args = []):
    self.name = fname
    self.args = args
    self.type = type

  def __str__(self):
    if len(self.args) > 0:
      arg_str = reduce(lambda s, a: s + ", " + str(a), self.args, "")
      return self.name + "(" + arg_str[2:] + ")"
    else:
      return self.name

  def __eq__(self, other):
    if isinstance(other,Fun) and self.name == other.name:
      return reduce(lambda b, (a1, a2): b and a1 == a2, zip(self.args, other.args), True)
    return False

  def ctrl(self, var_map):
    if len(self.args) > 0:
      arg_str = reduce(lambda s, a: s + ", " + a.ctrl(var_map), self.args, "")
      return self.name + "(" + arg_str[2:] + ")"
    else:
      return self.name
  
  def symbols(self):
    return reduce(lambda s, a: s + a.symbols(), self.args, [self.name])
  
  def variables(self):
    return reduce(lambda s, a: s + a.variables(), self.args, [])


def lctrs_binop(op, bits, signed):
  bool_ops = {
    "&&": "/\\",
    "||": "\\/"
  }
  bv_ops_u = {
    "==": "=",
    "!=": "!=",
    "+": "+",
    "*": "*",
    "-": "-",
    "&": "&",
    "||": "|",
    "<<": "<<"
  }
  bv_ops_s = {
    "/": "/",
    "%": "%",
    "<": "<",
    ">": ">",
    "<=": "<=",
    ">=": ">="
  }
  if op in bool_ops:
    return bool_ops[op]
  elif op in bv_ops_u:
    return bv_ops_u[op] + "." + str(bits)
  elif op in bv_ops_s:
    return bv_ops_s[op] + ("s" if signed else "u") + "." + str(bits)
  else:
    return "(unknown binop)"


def lctrs_unop(op, bits, signed):
  bool_ops = {
    "!": "not"
  }
  bv_ops_u = {
    "~" : "~",
    "-" : "neg",
  }
  if op in bool_ops:
    return bool_ops[op]
  elif op in bv_ops_u:
    return bv_ops_u[op] + "." + str(bits)
  else:
    return "(unknown unop)"

class TheoryFun(Term):
  def __init__(self, fname, type, args = []):
    self.name = fname
    self.type = type
    self.args = args

  @classmethod
  def const(cls, val, type):
    return cls(val, type, [])

  def __str__(self):
    if len(self.args) > 0:
      arg_str = reduce(lambda s, a: s + ", " + str(a), self.args, "")
      return self.name + "(" + arg_str[2:] + ")"
    else:
      return self.name

  def __eq__(self, other):
    if isinstance(other,TheoryFun) and self.name == other.name:
      return reduce(lambda b, (a1, a2): b and a1 == a2, zip(self.args, other.args), True)
    return False

  def ctrl(self, var_map):
    args = self.args
    if len(self.args) == 0: # value
      if self.type.isBool():
        return self.name
      else:
        assert(self.type.isInteger())
        val = int(self.name)
        hexval = hex(val)[2:] # cut off "x"
        # 0-pad
        mbits = self.type.bits/4 - len(hexval)
        hexval = reduce(lambda s, a: "0" + s, range(mbits), hexval)
        return "bv" + str(self.type.bits) + "\"#x" + hexval + "\""
    elif len(self.args) == 1: # unary
      op = lctrs_unop(self.name, self.type.bits, self.type.is_signed)
      return op + "(" + args[0].ctrl(var_map) + ")"
    elif len(self.args) == 2: # binary
      op = lctrs_binop(self.name, args[0].type.bits, self.type.is_signed)
      s0 = args[0].ctrl(var_map)
      s1 = args[1].ctrl(var_map)
      return "(" + s0 + " " + op + " " + s1 + ")"
  
  def symbols(self):
    return []
  
  def variables(self):
    return reduce(lambda s, a: s + a.variables(), self.args, [])

######################## rules #################################################
class Rule:
  def __init__(self, lhs, rhs, cond, name = ""):
    self.lhs = lhs
    self.rhs = rhs
    self.cond = cond
    self.name = name

  @classmethod
  def uncond(cls, lhs, rhs, name = ""):
    return cls(lhs, rhs, None, name)
  
  def __str__(self):
    s = str(self.lhs) + " -> " + str(self.rhs)
    s =  s + (" [" + str(self.cond) + "]" if self.cond else "")
    return s + " // " + self.name

  def ctrl(self):
    lvars = self.lhs.variables()
    rvars = self.rhs.variables()
    xvars = [x for x in rvars if not (x in lvars)]
    var_map = dict([ (v.name, "inp" + str(i)) for i,v in enumerate(xvars)])
    s = self.lhs.ctrl({}) + " -> " + self.rhs.ctrl(var_map)
    s =  s + (" [" + self.cond.ctrl(var_map) + "]" if self.cond else "") + ";"
    return s + " /* " + self.name + " */"

  def symbols(self):
    return list(set(self.lhs.symbols() + self.rhs.symbols()))

######################## lctrs #################################################
class LCTRS:
  def __init__(self, rules, entry, src = ""):
    self.rules = rules
    self.origin = src
    self.entry = entry

  def signature(self):
    syms = reduce(lambda s, a: s + a.symbols(), self.rules, [])
    return list(set(syms))

  def ctrl(self):
    res = "THEORY bitvectors32\n"
    res = res + "LOGIC  QF_UFBV\n"
    res = res + "SOLVER external\n"
    syms = reduce(lambda s, sym: s + ", " + sym, self.signature(), "")[2:]
    res = res + "SIGNATURE " + syms + "\n"
    res = res + "RULES\n"
    res = res + reduce(lambda s, a: s + "  " + a.ctrl() + "\n", self.rules, "")
    res = res + "NON-STANDARD IRREGULAR\n"
    res = res + "QUERY loops " + self.entry.ctrl({}) + "\n"
    res = res + "END OF FILE\n"
    res = res + "(converted from " + self.origin + ")\n"
    return res

  # connect l1 -> r1 [c] with l2 -> r2 to  l1 -> r2 [c] if
  # - the second rule is unconditional, and
  # - the second rule is the only one with this lhs
  def find_combinable(self):
    for i in range(len(self.rules)):
      rl1 = self.rules[i]
      matches = []
      for j in range(len(self.rules)):
        rl2 = self.rules[j]
        if not rl2.cond and rl1.rhs == rl2.lhs:
          matches.append((j, rl2))
      if len(matches) == 1:
        rl2 = matches[0][1]
        rl_new = Rule(rl1.lhs, rl2.rhs, rl1.cond, rl1.name + " + "+ rl2.name)
        return (i, matches[0][0], rl_new)
    return None
  
  def combine_rules(self):
    conn = self.find_combinable()
    if conn:
      i, j, rl_new = conn
      rl1 = self.rules[i]
      rl2 = self.rules[j]
      #print("combine " + str(rl1) + " and " + str(rl2) + " to " + str(rl_new))
      self.rules[i] = rl_new # replace rl at position i
      self.simplify()
    else:
      pass

  def dead_code_elim(self):
    dels = []
    for i in range(len(self.rules)):
      rl = self.rules[i]
      if rl.lhs.name == "main":
        continue
      # check whether there are rules which have root of rl in rhs
      # i.e., rl is reachable
      occ = [rl2 for rl2 in self.rules if rl2.rhs.name == rl.lhs.name]
      if len(occ) == 0:
        #print("delete " + str(rl))
        dels.append(i)
    
    dels.sort(reverse=True)
    for d in dels:
        del(self.rules[d])
    
  def simplify(self):
    self.combine_rules()
    #print("after combine")
    #print(self.ctrl())
    self.dead_code_elim()

    

######################## visitors ##############################################
# map over function definitions, get functions with types
# has to be done before next visitor due to mutual recursion/
class FuncTypeVisitor(c_ast.NodeVisitor):
  def __init__(self):
    self.funs = {}

  def visit_FuncDef(self, node):
    types = concat(node.decl.type.type.type.names)
    self.funs[node.decl.name] = Type.of_name(types)

# map over function definitions
class FuncDefVisitor(c_ast.NodeVisitor):
  def __init__(self, glob_vars, funs):
    self.glob_vars = glob_vars
    self.funs = funs
    self.rules = []
    self.entry = None

  def visit_FuncDef(self, node):
    types = concat(node.decl.type.type.type.names)
    self.funs[node.decl.name] = Type.of_name(types)
    rules, entry = collect_rules_for_func(node, self.glob_vars, self.funs)
    self.rules = self.rules + rules
    if entry.name == "main":
      self.entry = entry

# colect global variables
class GlobalVarVisitor(c_ast.NodeVisitor):
  def __init__(self):
    self.vars = []
  
  def visit_FuncDef(self, node):
    pass
  
  def visit_Decl(self, node):
    if hasattr(node.type.type, "names"): # variables
      typename = concat(node.type.type.names)
      var = (node.name, Var(node.name, Type.of_name(typename)))
      self.vars.append(var)

# create term from expression
class ExprVisitor(c_ast.NodeVisitor):
  def __init__(self, vars, glob_vars, funs):
    self.exprs = [] # expression stack
    self.vars = vars
    self.glob_vars = glob_vars
    self.funs = funs 

  def visit_ID(self, node): # variable
    expr = None
    if node.name == "true": # cyparser does not recognize
      expr = TheoryFun(str("true"), Type.of_name("bool"))
    elif node.name == "false": # cyparser does not recognize
      expr = TheoryFun(str("false"), Type.of_name("bool"))
    else:
      expr = dict(self.vars)[node.name]
    self.exprs = [expr] + self.exprs

  def visit_Constant(self, con):
    self.exprs = [TheoryFun(str(con.value), Type.of_name(con.type))] +self.exprs

  def visit_UnaryOp(self, node):
    self.visit(node.expr)
    arg = self.exprs[0]
    self.exprs = [TheoryFun(str(node.op), arg.type, [arg])] + self.exprs[1:]

  def visit_BinaryOp(self, node):
    self.visit(node.left)
    self.visit(node.right)
    right = self.exprs[0]
    left = self.exprs[1]
    # TODO
    assert (left.type == right.type)
    res_type = Type.mkBool() if node.op in ["==", "!=", "<", ">", "<=", ">="] else left.type
    self.exprs = [TheoryFun(node.op, res_type, [left, right])] + self.exprs[2:]

  def visit_FuncCall(self, node):
    if node.name.name == "__VERIFIER_nondet_int":
      fresh_var = Var("rnd" + str(len(self.vars)), Type(Type.INT, 32, True))
      self.exprs = [fresh_var] + self.exprs
    elif node.name.name == "__VERIFIER_nondet_uint":
      fresh_var = Var("rnd" + str(len(self.vars)), Type(Type.INT, 32, False))
      self.exprs = [fresh_var] + self.exprs
    else:
      fname = node.name.name
      fun_type = self.funs[fname]
      args = [v for _, v in self.glob_vars]
      if hasattr(node.args, "exprs"):
        for a in node.args.exprs:
          self.visit(a)
        args = self.exprs[:len(node.args.exprs)] # take top n expressions from stack
        args.reverse()
      self.exprs = [Fun(fname, fun_type, args)] + self.exprs

  def getExpr(self, type = None):
    e = self.exprs[0]
    if not type or type == e.type:
      return e
    elif type == Type.mkBool() and e.type.type == Type.INT:
      return TheoryFun("!=", Type.mkBool(), [e, TheoryFun.const("0", e.type)])
    else:
      raise Exception('TODO: implement cast')

    

# collect rules
class BlockVisitor(c_ast.NodeVisitor):
  def __init__(self, fun_name, vars, glob_vars, funs, count = 0):
    self.fun_name = fun_name
    self.vars = vars
    self.glob_vars = glob_vars
    self.funs = funs
    self.rules = []
    self.line_count = count # last-used rhs index
    self.returns = False    

  def mk_fun(self, cnt):
    fun_type = self.funs[self.fun_name]
    return Fun("u_" + self.fun_name + str(cnt), fun_type, self.vars_list())

  def mk_fun_with(self, cnt, args):
    fun_type = self.funs[self.fun_name]
    return Fun("u_" + self.fun_name + str(cnt), fun_type, args)

  def mk_return(self, expr, name = None):
    name = name if name != None else self.fun_name
    fun_type = self.funs[name]
    return Fun("return_" + str(name), fun_type, [expr])

  def vars_list(self):
    return [v for _, v in self.vars]

  def mkExprVisitor(self):
    return ExprVisitor(self.vars, self.glob_vars, self.funs)

  def visit_Decl(self, node): # todo: more elegant way to get rid of main?
    if node.name != self.fun_name:
      assert(isinstance(node.type.type, c_ast.IdentifierType))
      typename = concat(node.type.type.names)

      lhs = self.mk_fun(self.line_count)
      self.vars.append((node.name, Var(node.name, Type.of_name(typename))))
      rhs = self.mk_fun(self.line_count + 1)
      self.rules.append(Rule.uncond(lhs, rhs, "declare " + node.name))
      self.line_count = self.line_count + 1

  def visit_Assignment(self, node):
    assert(isinstance(node.lvalue, c_ast.ID)) 
    v = self.mkExprVisitor()
    v.visit(node.rvalue)
    rexpr = v.getExpr()
    lhs = self.mk_fun(self.line_count)
    assigned = node.lvalue.name
    rargs = [rexpr if n == assigned else x for n, x in self.vars]
    rhs = self.mk_fun_with(self.line_count + 1, rargs)
    rule = Rule.uncond(lhs, rhs, "assign " + assigned)
    self.rules.append(rule)
    self.line_count = self.line_count + 1

  def visit_UnaryOp(self, node):
    assert(isinstance(node.expr, c_ast.ID))
    assigned = node.expr.name

    # determine rhs of assignment
    var = dict(self.vars)[assigned]
    type = var.type
    exprs = {
      "++" : TheoryFun("+", type, [var, TheoryFun.const("1", type)]),
      "--" : TheoryFun("-", type, [var, TheoryFun.const("1", type)]),
      "p++" : TheoryFun("+", type, [var, TheoryFun.const("1", type)]), # post
      "p--" : TheoryFun("-", type, [var, TheoryFun.const("1", type)])  # post
    }
    assert(node.op in exprs)

    lhs = self.mk_fun(self.line_count)
    rargs = [exprs[node.op] if n == assigned else x for n, x in self.vars]
    rhs = self.mk_fun_with(self.line_count + 1, rargs)
    rule = Rule.uncond(lhs, rhs, "unary op " + node.op + assigned)
    self.rules.append(rule)
    self.line_count = self.line_count + 1

  def visit_Return(self, node):
    v = self.mkExprVisitor()
    v.visit(node.expr)
    rexpr = v.getExpr()
    lhs = self.mk_fun(self.line_count)
    rule = Rule.uncond(lhs, self.mk_return(rexpr))
    self.rules.append(rule)
    self.returns = True

  def visit_If(self, node):
    v = self.mkExprVisitor()
    v.visit(node.cond)
    cond = v.getExpr(Type.mkBool())
    cnt = self.line_count

    # if true
    lhs = self.mk_fun(cnt)
    rhs_true = self.mk_fun(cnt + 1)
    self.rules.append(Rule(lhs, rhs_true, cond, "if"))
    tvis = BlockVisitor(self.fun_name, list(self.vars), self.glob_vars, self.funs, cnt + 1)
    tvis.visit(node.iftrue)
    self.rules = self.rules + tvis.rules
    cnt = tvis.line_count + 1
    phi = cnt
    neg_cond = TheoryFun("!", Type.mkBool(), [cond])

    # if false
    if node.iffalse != None:
      rhs_false = self.mk_fun(cnt)
      self.rules.append(Rule(lhs, rhs_false, neg_cond, "else"))
      fvis = BlockVisitor(self.fun_name, list(self.vars), self.glob_vars, self.funs, cnt)
      fvis.visit(node.iffalse)
      self.rules = self.rules + fvis.rules
      cnt = fvis.line_count
      phi = cnt + 1 
      if not fvis.returns:
        # edge from else branch to phi node
        rule = Rule.uncond(fvis.mk_fun(cnt), self.mk_fun(phi), "phi else")
        self.rules.append(rule)
    else:
      # no else branch exists
      self.rules.append(Rule(lhs, self.mk_fun(phi), neg_cond, "skip else"))

    # edge from if branch to phi node
    if not tvis.returns:
      rl = Rule.uncond(tvis.mk_fun(tvis.line_count), self.mk_fun(phi), "phi if")
      self.rules.append(rl)
    #print("after if", rules_str(self.rules, 2))
    self.line_count = phi
    

  def visit_While(self, node):
    v = self.mkExprVisitor()
    v.visit(node.cond)
    cond = v.getExpr(Type.mkBool())
    cnt = self.line_count

    # loop condition true
    check_loop = self.mk_fun(cnt)
    into_loop = self.mk_fun(cnt + 1)
    self.rules.append(Rule(check_loop, into_loop, cond, "while condition true"))
    loop_vis = BlockVisitor(self.fun_name, list(self.vars), self.glob_vars, self.funs, cnt + 1)
    loop_vis.visit(node.stmt)
    self.rules = self.rules + loop_vis.rules
    end_loop = loop_vis.mk_fun(loop_vis.line_count)
    self.rules.append(Rule.uncond(end_loop, check_loop, "while back edge"))

    # loop condition false
    after_loop = self.mk_fun(loop_vis.line_count + 1)
    neg_cond = TheoryFun("!", Type.mkBool(), [cond])
    self.rules.append(Rule(check_loop, after_loop, neg_cond, "exit while"))

    self.line_count = loop_vis.line_count + 1
    

  def visit_For(self, node):
    # init
    self.visit(node.init)

    # get expression for condition
    v = self.mkExprVisitor()
    v.visit(node.cond)
    cond = v.getExpr(Type.mkBool())
    cnt = self.line_count

    # loop condition true
    check_loop = self.mk_fun(cnt)
    into_loop = self.mk_fun(cnt + 1)
    self.rules.append(Rule(check_loop, into_loop, cond, "for condition true"))
    loop_vis = BlockVisitor(self.fun_name, list(self.vars), self.glob_vars, self.funs, cnt + 1)
    loop_vis.visit(node.stmt)
    loop_vis.visit(node.next)
    self.rules = self.rules + loop_vis.rules
    end_loop = loop_vis.mk_fun(loop_vis.line_count)
    self.rules.append(Rule.uncond(end_loop, check_loop, "for back edge"))

    # loop condition false
    after_loop = self.mk_fun(loop_vis.line_count + 1)
    neg_cond = TheoryFun("!", Type.mkBool(), [cond])
    self.rules.append(Rule(check_loop, after_loop, neg_cond, "exit for"))

    self.line_count = loop_vis.line_count + 1


  def visit_FuncCall(self, node):
    v = self.mkExprVisitor()
    v.visit(node)
    call = v.getExpr()
    #assert(call.type == Type.mkVoid()) not true for SV comp examples
    
    call_term = self.mk_fun_with(self.line_count + 1, [v for _,v in self.vars] + [call])
    ret_term = self.mk_fun_with(self.line_count + 1, [v for _,v in self.vars] + [Var("ret", Type.mkVoid())])
    self.rules.append(Rule.uncond(self.mk_fun(self.line_count), call_term, "call"))
    self.rules.append(Rule.uncond(ret_term, self.mk_fun(self.line_count + 2), "return"))

    #print(rules_str(self.rules, 2))
    self.line_count = self.line_count + 2

  
################################################################################

def collect_rules_for_func(fnode, glob_vars, funs):
  name = fnode.decl.name

  params = list(glob_vars) # copy
  if fnode.decl.type.args:
    for p in fnode.decl.type.args:
      types = concat(p.type.type.names)
      if types != "void": # skip void unlock(void) etc
        params.append((p.name, Var(p.name, Type.of_name(types))))

  entry = Fun(name, funs[name], [p for _, p in params])
  vis = BlockVisitor(name, params, glob_vars, funs)
  start = vis.mk_fun(0)
  vis.visit(fnode)
  rules = [Rule.uncond(entry, start)] + vis.rules
  return rules, entry

def translate_funcs(src_file_name, ast):
  gvv = GlobalVarVisitor()
  gvv.visit(ast)
  glob_vars = gvv.vars

  ftv = FuncTypeVisitor()
  ftv.visit(ast)
  func_types = ftv.funs

  func_vis = FuncDefVisitor(glob_vars, func_types)
  func_vis.visit(ast)
  lctrs = LCTRS(func_vis.rules, func_vis.entry, src_file_name)
  #print lctrs.ctrl()
  #lctrs.simplify()
  return lctrs.ctrl()

def convert(src_file_name):
  src_file = open(src_file_name, "r")
  src = src_file.read()
  src = comment_remover(src)

  # parse
  parser = c_parser.CParser()
  ast = parser.parse(src)
  #ast.show(offset=2)

  return translate_funcs(src_file_name, ast)

def get_expected_verdict(yml):
  #  - property_file: ../properties/termination.prp
  #    expected_verdict: true
  if os.path.exists(yml):
    file = open(yml, "r") 
    props = file.read()
    if not ("termination.prp" in props):
      return "?"
    res = re.search('termination.prp\s+expected_verdict: (\w+)', props)
    if res:
      return res.groups()[0]
    else:
      return "??"
  else:
    #WhileTrueInc_false-no-overflow_false-termination.c
    res = re.search('_(\w+)-termination', yml)
    if res:
      return res.groups()[0]
    else:
      return "err"




def work(problem):
  input = str(problem["dir"]) + "/" + problem["file"]
  problem["output_dir"]
  base = os.path.splitext(os.path.basename(problem["file"]))[0]
  yaml = str(problem["dir"]) + "/" + base + ".yml"
  exp = get_expected_verdict(yaml)
  output = problem["output_dir"] + "/" + base + "_" + str(problem["id"]) + ".ctrs"
  r = { "id" : problem["id"], "dir" : problem["dir"], "file": problem["file"], "expected":"?"}
  if not (exp == "false"):
    r["expected"] = "YES or ?"
    r["result"] = "SKIP"
    return r
  try:
    #print( str(problem["id"]) + ": " + base)
    lctrs = convert(input)
    f = open(output, "a")
    f.write(lctrs)
    f.close()
    with tempfile.NamedTemporaryFile() as temp:
      cmd = "./sandbox 20 ./ctrl {} 2>1 > {}".format(output, temp.name)
      #print(cmd)
      out,err = subprocess.Popen(cmd, shell=True).communicate()
      file = open(temp.name, "r") 
      res = file.read()
      if "NO" in res:
        r["result"] = "NO"
      elif "YES" in res:
        r["result"] = "YES"
      elif "TIMEOUT" in res:
        r["result"] = "TIMEOUT"
      elif "MAYBE" in res:
        r["result"] = "MAYBE"
      else:
        r["result"] = "CTRL_ERROR"
      exp = get_expected_verdict(yaml)
      r["expected"] = "NO" if exp == "false" else "YES" if exp == "true" else exp
  except plyparser.ParseError:
    r["result"] = "PARSE_ERROR"
  except KeyError:
    r["result"] = "ERROR"
  except AssertionError:
    r["result"] = "ERROR"
  return r

def count_result(r, stats):
  if r["result"] != "SKIP":
    print(str(r["id"]) + " " + r["file"] + ": " + r["result"] + ("  (expected " + r["expected"] + ")" if r["result"] != "SKIP" else ""))
  if r["expected"] == "NO":
    stats['EXP_NO'] = stats['EXP_NO'] + 1
  if r['result'] == "NO":
    stats['NO'] = stats['NO'] + 1
  if r['result'] == "YES":
    stats['YES'] = stats['YES'] + 1
  elif r['result'] == "TIMEOUT":
    stats['TIMEOUT'] = stats['TIMEOUT'] + 1
  elif r['result'] == "MAYBE":
    stats['MAYBE'] = stats['MAYBE'] + 1
  elif r['result'] == "CTRL_ERROR":
    stats['CTRL_ERROR'] = stats['CTRL_ERROR'] + 1
  elif r['result'] == "PARSE_ERROR":
    stats['PARSE_ERROR'] = stats['PARSE_ERROR'] + 1
  elif r['result'] == "SKIP":
    stats['SKIP'] = stats['SKIP'] + 1
  else:
    stats['ERROR'] = stats['ERROR'] + 1

def accumulate(results, stats):
  for r in results:
    count_result(r, stats)


if __name__ == "__main__":
  if len(sys.argv) < 2:
    print("usage: c2lctrs.py <c file or directory>")

  # get source file or directory
  src = sys.argv[1]
  if not os.path.isdir(src):
    print(convert(src))
  else:
    dst = sys.argv[2] if len(sys.argv) > 2 else "lctrss"

    i = 0
    jobs = []
    stats = {
      "NO": 0,
      "YES": 0,
      "MAYBE": 0,
      "TIMEOUT": 0,
      "PARSE_ERROR": 0,
      "ERROR": 0,
      "CTRL_ERROR": 0,
      "SKIP": 0,
      "EXP_NO": 0
    }
    for subdir, dirs, problems in os.walk(src):
      for p in problems:
        if os.path.splitext(p)[1] in [".c", ".C"]:
          job = { "id" : i, "dir": subdir, "file" : p, "output_dir" : dst}
          jobs.append(job)
          i = i + 1
          count_result(work(job), stats)

    # run jobs
    numprocs = 1
    print("Doing %d jobs with %d processes" % (i,numprocs))
    pool = multiprocessing.Pool(numprocs)
    total_tasks = i
    #results = pool.map_async(work, jobs)
    pool.close()
    #pool.join()
    #accumulate(results.get(), stats)
    print("%d YES, %d NO (%d), %d MAYBE, %d timeouts, %d errors, %d ctrl errors, %d parse errors, %d skipped" % (stats['YES'],stats['NO'],stats['EXP_NO'], stats['MAYBE'], stats['TIMEOUT'], stats['ERROR'], stats['CTRL_ERROR'], stats['PARSE_ERROR'], stats['SKIP']))
