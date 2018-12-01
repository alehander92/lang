# object A[T]?:
#   a:      Int
#   b:      Float
#   c:      Dict[T, Int]
#   e:      A[T]?

# enum E:
#   Blue, Green

# data Node:
#   InfixOp(Int, Node, Node)
#   Lit(Float)

import macros, sequtils, strformat, strutils, algorithm, options, sugar, tables

type
  NodeKind* = enum 
    Program,
    Signature,
    FunctionDef,
    Code,
    IfNode,
    InfixOp,
    Operator,
    Args,
    Name,
    Int,
    Call,
    Assign,
    Declaration,
    DeclarationHelper,
    ForRange,
    ForIn,
    ReturnNode,
    BigO,
    ComplexitySignature


  Node* = ref object
    case kind*: NodeKind:
    of Name, Operator:
      name*: string
    of Int:
      i*:    int
    of DeclarationHelper:
      declaration*: DeclarationKind
    else:
      children*: seq[Node]
    typ*: Type

  DeclarationKind = enum DeclLet, DeclVar

  TypeKind* = enum
    TSimple,
    TConcrete,
    TGeneric


  Type* = object
    case kind*: TypeKind:
    of TSimple:
      discard      
    of TConcrete:
      params*:  seq[Type]
      base*:    seq[Type]
    of TGeneric:
      args*:    seq[string]
    name*:      string


  TypeEnv* = ref object
    previous*: seq[TypeEnv]
    types*:    Table[string, Type]


proc check*(node: Node, env: TypeEnv)
proc checkChildren*(nodes: seq[Node], env: TypeEnv)

proc newTypeEnv*: TypeEnv =
  TypeEnv(previous: @[], types: initTable[string, Type]())

proc `[]`*(env: TypeEnv, name: string): Type =
  var current = env
  while true:
    if current.types.hasKey(name):
      return current.types[name]
    if current.previous.len > 0:
      current = current.previous[0]
    else:
      break
  return Type(kind: TSimple, name: "")

proc `[]=`*(env: TypeEnv, name: string, t: Type) =
  var types = env.types
  types[name] = t
  env.types = types

proc text*(node: Node, depth: int): string =
  if node.isNil:
    return repeat("  ", depth) & "nil"
  result = case node.kind:
    of Name, Operator:
      $node.name
    of Int:
      $node.i
    of DeclarationHelper:
      $node.declaration
    else:
      $node.kind & ":\n" & node.children.mapIt(it.text(depth + 1)).join("\n")
  result = repeat("  ", depth) & result

proc `$`*(node: Node): string =
  text(node,  0)

proc op*(name: string): Node =
  Node(kind: Operator, name: name)

proc decl*(a: DeclarationKind): Node =
  Node(kind: DeclarationHelper, declaration: a)

macro init*(kindValue: untyped, childrenValue: varargs[untyped]): untyped =
  var childrenNode = quote do: @[]
  for value in childrenValue:
    childrenNode[1].add(value)
  result = quote:
    Node(kind: `kindValue`, children: `childrenNode`)

proc init*(kind: NodeKind, i: int): Node =
  assert kind == Int
  Node(kind: Int, i: i)

proc init*(kind: NodeKind, name: string): Node =
  assert kind == Name
  Node(kind: Name, name: name)

  
proc pseudoNode(child: NimNode, depth: int = 0): NimNode

proc slice(child: NimNode, start: int): NimNode =
  result = newTree(child.kind)
  for i in start ..< child.len:
    result.add(child[i])
macro program*(children: untyped): untyped =
  result = quote:
    Program.init()
  
  for child in children:
    result.add(pseudoNode(child))


proc pseudoNode(child: NimNode, depth: int = 0): NimNode =
  # echo repeat("  ", depth), child.repr
  case child.kind:
  of nnkCall, nnkCallStrLit:
    let name = child[0].repr.capitalizeAscii
    if name.startsWith("Op") or name.startswith("Decl") and name != "Declaration":
      return child
    let nameNode = name.ident
    var values: NimNode
    if child.len > 1 and child[1].kind == nnkStmtList:
      values = child[1]
    else:
      values = child.slice(1)
    var call = quote:
      `nameNode`.init()
    for value in values:
      call.add(pseudoNode(value, depth + 1))
    result = call
  of nnkStrLit, nnkRStrLit:
    result = quote do: Name.init(`child`)
  of nnkIntLit:
    result = quote do: Int.init(`child`)
  of nnkStmtList:
    result = pseudoNode(child[0], depth + 1)
  else:
    result = child
  # echo repeat("  ", depth), "result", result.repr


let code = program:
  signature("Int", "Int")
  functionDef("fib", args("n")):
    code:
      ifNode:
        code:
          infixOp(op"<", "n", 2)
          infixOp(op"+", call("fib", infixOp(op"-", "n", 1), infixOp(op"-", "n", 2)))
        code:
          1
  call("fib", 4)

using
  node: Node
  env: TypeEnv

macro genCase(t: NodeKind, name: untyped, args: varargs[untyped]): untyped =
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(args[0], ident"kind"))
  for a in NodeKind.low .. NodeKind.high:
    let aNode = ident($a)
    let callName = ident(name.repr & ($a)[0 .. ^1].capitalizeAscii)
    let child = ident"child"
    var call = nnkCall.newTree(callName)
    var childCall = nnkCall.newTree(name, child)
    for i, arg in args:
      call.add(arg)
      if i > 0:
        childCall.add(arg)
    let code = quote:
      when declared(`callName`):
        echo "=> ", node.kind
        `call`
      else:
        # echo "NO ", node.kind
        for `child` in node.children:
          `childCall`

    result.add(nnkOfBranch.newTree(aNode, code))

proc `[]`*(node; index: int): Node =
  node.children[index]

proc `[]=`*(node; index: int, value: Node): Node =
  node.children[index] = value



proc checkName*(node, env) =
  let t = env[node.name]
  if t.name.len == 0:
    for name, typ in env.types:
      echo name, " ", typ.name
    echo &"NO {node.name}"
    quit(1)
  else:
    node.typ = t

proc checkInt*(node, env) =
  node.typ = env["Int"]

proc checkString*(node, env) =
  node.typ = env["String"]

proc genType*(node, env): Type =
  Type(kind: TSimple, name: node.name)

proc checkComplexitySignature*(node, env) =
  discard

proc checkFunctionDef*(node, env) =
  var t = Type(kind: TConcrete, name: "Function")
  var signature: Node
  var args: Node
  var code: Node
  var name: string
  if node[0].kind == ComplexitySignature: 
    (signature, args, code) = (node[1], node[3], node[4])
    name = node[2].name
  else:
    (signature, args, code) = (node[0], node[2], node[1])
    name = node[1].name
  for child in signature.children: # args
    t.params.add(genType(child, env))
  node.typ = t
  let existing = env[name]
  if existing.name.len > 0:
    echo &"Overriding {name}"
    quit(1)
  env[name] = t
  var childEnv = newTypeEnv()
  childEnv.previous = @[env]
  for i, arg in args.children:
    childEnv[arg.name] = t.params[i]
    echo arg.name
  check(code, childEnv)
  
proc checkOperator(node, env) =
  discard

template expect(t: Type, u: string): untyped =
  if t.kind != TSimple or t.name != u:
    echo "not " & $u
    quit(1)


proc checkIfNode(node, env) =
  check(node[0], env)
  if node[0].typ.kind != TSimple or node[0].typ.name != "Bool":
    echo &"no bool"
    quit(1)
  check(node[1], env)

proc checkCode(node, env) =
  checkChildren(node.children, env)

proc checkInfixOp(node, env) =
  check(node[1], env)
  check(node[2], env)
  let l = node[1].typ
  let r = node[2].typ

  case node[0].name:
  of "+", "-", "*", "/":
    expect(l, "Int")
    expect(r, "Int")
    node.typ = env["Int"]
  of "==", "<", ">":
    expect(l, "Bool")
    expect(r, "Bool")
    node.typ = env["Bool"]
  else:
    echo &"operator {node[0].name}"
    quit(1)

proc checkProgram*(node, env) =
  for i, child in node.children:
    case child.kind:
    of FunctionDef:
      # signature
      child.children = @[node.children[i - 1]].concat(child.children)
      echo "=> ", child.kind
      checkFunctionDef(child, env)
    of Signature:
      discard
    else:
      check(child, env)

proc check*(node, env) =
  genCase(NodeKind.low, check, node, env)

proc checkChildren*(nodes: seq[Node]; env) =
  for node in nodes:
    check(node, env)

var env = newTypeEnv()
env["Int"] = Type(kind: TSimple, name: "Int")
env["String"] = Type(kind: TSimple, name: "String")
env["Bool"] = Type(kind: TSimple, name: "Bool")


# n -> O[n^2]
# Int -> Int
# def example0(n):
#   var result = 0
#   for i in 0 ..< n:
#     for j in 0 ..< n:
#       result = result + j
#   return result

let example0 = program:
  complexitySignature("n", bigO(infixOp(op"^", "n", 2)))
  signature("Int", "Int")
  functionDef("example0", args("n")):
    code:
      declaration(decl(DeclVar), assign("result", 0))
      forRange("i", 0, "n"):
        forRange("j", 0, "n"):
          assign("result", infixOp(op"+", "result", "j"))
      returnNode("result")

type
  ComplexityEnv* = ref object
    typeEnv*:    TypeEnv
    previous*:   seq[ComplexityEnv]
    facts*:      Table[string, SyExpression]
  
  SyKind* = enum Symbol, SyPlus, SyMinus, SyMul, SyDiv, SyPower, SySum, SyInt, SyText

  SyExpression* = ref object
    case kind*: SyKind:
    of Symbol:
      name*:     string
    of SyPower, SyPlus, SyMul, SyDiv, SyMinus:
      left*:     SyExpression
      right*:    SyExpression
    of SySum:
      start*:    SyExpression
      finish*:   SyExpression
      child*:    SyExpression
    of SyInt:
      i*:        int
    of SyText:
      text*:     string

proc `[]`(cenv: ComplexityEnv, name: string): SyExpression =
  var now = cenv
  if now.isNil:
    return nil
  elif now.facts.hasKey(name):
    return now.facts[name]
  elif cenv.previous.len == 0:
    return nil
  else:
    return cenv.previous[0][name]

proc `[]=`(cenv: ComplexityEnv, name: string, exp: SyExpression) =
  cenv.facts[name] = exp

proc sy*(name: string): SyExpression =
  SyExpression(kind: Symbol, name: name)


converter toSymbol*(i: int): SyExpression =
  SyExpression(kind: SyInt, i: i)

proc `==`*(l: SyExpression, r: SyExpression): bool =
  if l.isNil or r.isNil:
    return false
  if l.kind != r.kind:
    return false
  case l.kind:
  of SyPlus, SyMinus, SyPower, SyMul, SyDiv:
    l.left == r.left and l.right == r.right
  of SySum:
    l.start == r.start and l.finish == r.finish and l.child == r.child
  of Symbol:
    l.name == r.name
  of SyInt:
    l.i == r.i
  of SyText:
    l.text == r.text

using
  l: SyExpression
  r: SyExpression

proc `+`*(l, r): SyExpression =
  if l.isNil:
    r
  elif r.isNil:
    l
  else:
    SyExpression(kind: SyPlus, left: l, right: r)

proc `-`*(l, r): SyExpression =
  if l.isNil:
    r
  elif r.isNil:
    l
  else:
    SyExpression(kind: SyMinus, left: l, right: r)

proc text(a: SyExpression, depth: int = 0): string =
  if a.isNil:
    return repeat("  ", depth) & "nil"
  result = repeat("  ", depth) & $a.kind
  let right = case a.kind:
    of Symbol:
      &"[{a.name}]"
    of SyPower, SyPlus, SyMinus, SyMul, SyDiv:
      &":\n{text(a.left, depth + 1)}\n{text(a.right, depth + 1)}\n"
    of SySum:
      &"Sum:\n  {text(a.start, depth + 1)}\n {text(a.finish, depth + 1)}\n{text(a.child, depth + 1)}"
    of SyInt:
      &"[{a.i}]"
    of SyText:
      &"[{a.text}]"
  result = result & right

proc initComplexityEnv*(previous: seq[ComplexityEnv], typeEnv: TypeEnv): ComplexityEnv =
  ComplexityEnv(previous: previous, typeEnv: typeEnv, facts: initTable[string, SyExpression]())

var cenv = initComplexityEnv(@[], env)

using
  cenv: ComplexityEnv

proc signify*(node, cenv): SyExpression =
  case node.kind:
  of Int:
    result = node.i
  of Name:
    let exp = cenv[node.name]
    if exp.isNil:
      result = 0
    else:
      result = exp
  else:
    result = 0

proc complexity*(node: Node, cenv: ComplexityEnv): SyExpression

proc complexityForRange*(node, cenv): SyExpression =
  # start a sum!
  var e = SyExpression(kind: SySum)
  e.start = signify(node[1], cenv)
  e.finish = signify(node[2], cenv)
  e.child = complexity(node[3], cenv)
  e



proc simplify(exp: SyExpression): SyExpression

proc simplifyBasic(exp: SyExpression): SyExpression =
  case exp.kind:
  of SyPlus, SyMinus, SyMul:
    let l = exp.left.simplifyBasic
    let r = exp.right.simplifyBasic
    if exp.kind in {SyPlus, SyMinus}:
      if l.kind == SyInt:
        result = r
      elif r.kind == SyInt:
        result = l
      else:
        result = if exp.kind == SyPlus:
            if l == r:
              SyExpression(kind: SyMul, left: 2, right: l)
            else:
              SyExpression(kind: SyPlus, left: l, right: r)
          else:
            if l == r:
              SyExpression(kind: SyInt, i: 0)
            else:
              SyExpression(kind: SyMinus, left: l, right: r)
    else:
      if l.kind == SyInt and l.i == 0:
        result = SyExpression(kind: SyInt, i: 0)
      elif l.kind == SyInt and r.kind == SyInt:
        result = SyExpression(kind: SyInt, i: l.i * r.i)
      elif l == r:
        result = SyExpression(kind: SyPower, left: l, right: 2)
      else:
        result = exp

  of SySum:
    let coefficient = exp.finish.simplifyBasic - exp.start.simplifyBasic
    result = SyExpression(kind: SyMul, left: coefficient, right: exp.child)
  else:
    result = exp
  echo "basic", text(exp), " text", text(result), "\n\n"

proc simplify(exp: SyExpression): SyExpression =
  var current: SyExpression = nil
  var nextExp = exp
  while current != nextExp:
    current = nextExp
    nextExp = nextExp.simplifyBasic
    break
  result = nextExp

proc complexityFunctionDef*(node, cenv): SyExpression =
  echo node
  if node[0].kind != ComplexitySignature:
    return

  var childCenv = initComplexityEnv(@[cenv], nil)

  for i, arg in node[3].children:
    childCenv[arg.name] = SyExpression(kind: Symbol, name: node[0][i].name)
  let code = node[4]
  var exp = toSymbol(0)
  for child in code.children:
    let e2 = complexity(child, childCenv)
    exp = exp + e2
  discard text(simplify(exp))
  
proc complexityProgram*(node, cenv): SyExpression =
  for i, child in node.children:
    echo "=> ", child.kind
    case child.kind:
    of ComplexitySignature:
      node.children[i + 2].children = @[child].concat(node.children[i + 2].children)
    of FunctionDef:
      discard complexityFunctionDef(child, cenv)
    else:
      discard

proc complexity*(node, cenv): SyExpression =
  case node.kind:
  of Program:
    complexityProgram(node, cenv)
  of ForRange:
    complexityForRange(node, cenv)
  else:
    1
  

proc complexityCheck*(node, cenv) =
  discard complexity(node, cenv)

check(example0, env)
echo example0
complexityCheck(example0, cenv)
  





# n -> O[n^2]
# Int -> Int
# def example1(n):
#   var result = 0
#   for i in 0 ..< n:
#     for j in i ..< n:
#       result += j
#   return result

# example0
# for:  n
#   for : n 
#     code: 1
#   n
# n * n <=> n^2

# example1
# for: n
#   for: n - i
#     code: 1
#   n - i
# sum(0, n, n - i)
# n - 0 + n - 1 + n - 2 .. + n - (n - 1)
# n * n - (n - 1) * (n - 2) / 2
# n^2 - 0.5n^2 - 1.5 * n + 1
# 0.5n^2 - 1.5*n <=> n^2

# we need symbolic math
# seems hard to do
# maybe we can just special case several cases

# lets see

# n -> O[n^2]
# Int
# def example2(n):
#   var result = 0
#   for i in 0 ..< n:
#     if i < 1:
#       example0(i)


# example2
# for: n
#   if: 1
#     example0: i ^ 2
# C != n^2
# we might need to expand all invocations..
# and on recursion say: unsupported

