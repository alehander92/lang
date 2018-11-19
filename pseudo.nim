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

  Node* = object
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
      name*:    string
    of TConcrete:
      params*:  seq[Type]
    of TGeneric:
      args*:    seq[string]
  
  TypeEnv* = object
    previous*: seq[TypeEnv]
    types*:    Table[string, Type]

proc initTypeEnv*: TypeEnv =
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
  functionDef("fib", args("n")):
    signature("Int", "Int")
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

proc checkName*(node, env) =
  let t = env[node.name]
  if t.len == 0:
    echo &"NO {node.name}"
  else:
    node.typ = t

proc checkInt*(node, env) =
  env["Int"]

proc check*(node, env) =
  genCase(NodeKind.low, check, node, env)

var env = initTypeEnv()
env["Int"] = Type(kind: TSimple, name: "Int")

check(code, env)
  
