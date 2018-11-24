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

  echo result.repr

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
        `call`
      else:
        echo "NO ", node.kind
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

proc checkFunctionDef*(node, env) =
  var t = Type(kind: TConcrete, name: "Function")
  for child in node[0].children: # args
    t.params.add(genType(child, env))
  node.typ = t
  let name = node[1].name
  let existing = env[name]
  if existing.name.len > 0:
    echo &"Overriding {name}"
    quit(1)
  env[name] = t
  var childEnv = newTypeEnv()
  childEnv.previous = @[env]
  for i, arg in node[2].children:
    childEnv[arg.name] = t.params[i]
    echo arg.name
  check(node[3], childEnv)
  
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
# env["Bool"] = Type(kind: TSimple, name: "Bool")
# check(code, env)

echo code.typ.kind


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
  
  SyKind* = enum Symbol, SyPlus, SyMinus, SyPower, SyInt, SyText

  SyExpression* = ref object
    case kind*: SyKind:
    of Symbol:
      name*:     string
    of SyPower, SyPlus, SyMinus:
      left*:     SyExpression
      right*:    SyExpression
    of SyInt:
      i*:        int
    of SyText:
      text*:     string

    

proc sy*(name: string): SyExpression =
  SyExpression(kind: Symbol, name: name)


converter toSymbol*(i: int): SyExpression =
  SyExpression(kind: SyInt, i: i)

using
  l: SyExpression
  r: SyExpression

proc `+`*(l, r): SyExpression =
  SyExpression(kind: SyPlus, left: l, right: r)

proc `-`*(l, r): SyExpression =
  SyExpression(kind: SyMinus, left: l, right: r)

proc text(a: SyExpression, depth: int = 0): string =
  if a.isNil:
    return repeat("  ", depth) & "nil"
  result = repeat("  ", depth) & $a.kind
  let right = case a.kind:
    of Symbol:
      &"[{a.name}]"
    of SyPower, SyPlus, SyMinus:
      &":\n{text(a.left, depth + 1)}\n{text(a.right, depth + 1)}\n"
    of SyInt:
      &"[{a.i}]"
    of SyText:
      &"[{a.text}]"
  result = result & right

var cenv = ComplexityEnv(typeEnv: env)

using
  cenv: ComplexityEnv

proc complexity*(node: Node, cenv: ComplexityEnv): SyExpression

proc complexityForRange*(node, cenv): SyExpression =
  discard

proc complexityFunctionDef*(node, cenv): SyExpression =
  if node[0].kind != ComplexitySignature:
    return

  var childCenv = ComplexityEnv(typeEnv: cenv.typeEnv, previous: @[cenv])

  var expr = toSymbol(0)
  echo node[2].children.len
  for child in node[2].children:
    let e = complexity(child, childCenv)
    expr = expr + e
    echo expr.text
  
proc complexityProgram*(node, cenv): SyExpression =
  for i, child in node.children:
    echo child.kind
    case child.kind:
    of ComplexitySignature:
      node.children[i + 1].children = @[child].concat(node.children[i + 1].children)
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
    echo "no", node.kind
    1
  

proc complexityCheck*(node, cenv) =
  discard complexity(node, cenv)

check(example0, env)
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

