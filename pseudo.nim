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
    Call

  Node* = ref object
    case kind*: NodeKind:
    of Name, Operator:
      name*: string
    of Int:
      i*:    int
    else:
      children*: seq[Node]
    typ*: Type

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
    if name.startsWith("Op"):
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
env["Bool"] = Type(kind: )
check(code, env)

echo code.typ.kind


n -> O[n^2]
Int -> Int
def example0(n):
  var result = 0
  for i in 0 ..< n:
    for j in 0 ..< n:
      result += j
  return result

n -> O[n^2]
Int -> Int
def example1(n):
  var result = 0
  for i in 0 ..< n:
    for j in i ..< n:
      result += j
  return result

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

n -> O[n^2]
Int
def example2(n):
  var result = 0
  for i in 0 ..< n:
    if i < 1:
      example0(i)


# example2
# for: n
#   if: 1
#     example0: i ^ 2
# C != n^2
# we might need to expand all invocations..
# and on recursion say: unsupported

