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

import macros, sequtils, strformat, strutils

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
      
echo code
