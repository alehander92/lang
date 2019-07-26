# Thank Lord!

import macros, strutils, sequtils, tables, strformat, algorithm, sugar, sets, hashes

type
  NodeKind* = enum 
    Program,
    Signature,
    Fn,
    Code,
    IfNode,
    InfixOp,
    Operator,
    Args,
    Name,
    Typename,
    Int,
    Number,
    Call,
    Assign,
    Declaration,
    PointerType,
    Arg,
    ForRange,
    ForIn,
    ReturnNode,
    BigO,
    ComplexitySignature,
    CallArgs,
    # Good
    RightCall,
    Index,
    BigM,
    ComplexityInfix,
    DeclarationName,
    RightInfix

  Node* = ref object
    case kind*: NodeKind:
    of Name, Operator, Typename, DeclarationName:
      name*: string
    of Int, Number:
      i*:    int
    else:
      children*: seq[Node]
    typ*: Type

  DeclarationKind = enum DeclLet, DeclVar

  TypeKind* = enum
    TSimple,
    TConcrete,
    TGeneric,
    TFunction,
    TPointer,
    TAny


  Type* = ref object
    case kind*: TypeKind:
    of TSimple, TAny:
      discard
    of TConcrete:
      params*:  seq[Type]
      base*:    seq[Type]
    of TGeneric:
      args*:    seq[string]
    of TFunction:
      functionArgs*: seq[Type]
    of TPointer:
      obj*:     Type
    name*:      string
    path*:      Path




  TypeEnv* = ref object
    previous*: seq[TypeEnv]
    types*: Table[string, Type]
    paths*: Table[Path, int]
    freed*: Table[Path, bool]
    lastName*: string

  Path* = ref object
    subPaths*: seq[string]

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


func path*(subPaths: seq[string]): Path =
  Path(subPaths: subPaths)
macro init*(kindValue: untyped, childrenValue: untyped): untyped =
  var childrenNode = childrenValue # quote do: @[]
  # for value in childrenValue:
  #   childrenNode[1].add(value)
  result = quote:
    Node(kind: `kindValue`, children: `childrenNode`)

proc init*(kind: NodeKind, i: int): Node =
  #assert kind == Int
  case kind:
  of Int:
    Node(kind: Int, i: i)
  of Number:
    Node(kind: Number, i: i)
  else:
    nil


proc init*(kind: NodeKind, name: string): Node =
  if kind == Name:
    Node(kind: Name, name: name)
  elif kind == Typename:
    Node(kind: Typename, name: name)
  elif kind == DeclarationName:
    Node(kind: DeclarationName, name: name)
  else:
    Node(kind: Operator, name: name)

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

proc `==`*(typ: Type, other: Type): bool =
  if typ.kind != other.kind:
    return false
  case typ.kind:
  of TAny:
    true
  of TSimple:
    typ.name == other.name
  of TConcrete, TGeneric:
    false
  of TFunction:
    typ.functionArgs.len == other.functionArgs.len and
      typ.functionArgs.zip(other.functionArgs).allIt(it[0] == it[1])
  of TPointer:
    typ.obj == other.obj
  
proc op*(name: string): Node =
  Node(kind: Operator, name: name)

proc decl*(a: string): Node =
  Node(kind: DeclarationName, name: a)

proc text*(node: Node, depth: int): string =
  if node.isNil:
    return repeat("  ", depth) & "nil"
  result = case node.kind:
    of Name, Operator, Typename, DeclarationName:
      $node.name
    of Int, Number:
      $node.i
    else:
      $node.kind & ":\n" & node.children.mapIt(it.text(depth + 1)).join("\n")
  result = repeat("  ", depth) & result


proc hash*(path: Path): Hash =
  path.subPaths.join("").hash 

proc `$`*(node: Node): string =
  text(node,  0)

proc `[]`*(node: Node; index: int): Node =
  node.children[index]

proc `[]=`*(node: Node; index: int, value: Node): Node =
  node.children[index] = value


proc `==`*(node: Node, other: Node): bool =
  if node.isNil or other.isNil:
    return false
  if node.kind != other.kind:
    return false
  case node.kind:
  of Name, Operator, Typename, DeclarationName:
    $node.name == $other.name
  of Int, Number:
    node.i == other.i
  else:
    false

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


using
  l: SyExpression
  r: SyExpression

proc `+`*(l: SyExpression, r): SyExpression =
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

proc text*(a: SyExpression, depth: int = 0): string =
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


proc `[]`*(cenv: ComplexityEnv, name: string): SyExpression =
  var now = cenv
  if now.isNil:
    return nil
  elif now.facts.hasKey(name):
    return now.facts[name]
  elif cenv.previous.len == 0:
    return nil
  else:
    return cenv.previous[0][name]


proc `[]=`*(cenv: ComplexityEnv, name: string, exp: SyExpression) =
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
