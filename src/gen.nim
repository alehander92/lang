# Praise God !



import types, macros, sequtils, strformat, strutils, algorithm, options, sugar, tables, tools

proc gen*(node: Node, context: var CGenerator)
proc genChildren*(nodes: seq[Node], context: var CGenerator)
proc genType*(typ: Type; context: var CGenerator)

using
  node: Node
  context: var CGenerator

template emit*(raw: string): untyped =
  context.output.add(raw)

template emit*(raw: static[string]): untyped =
  context.output.add(raw)

template emitLine*(raw: string): untyped =
  context.output.add(repeat(' ', context.indent * context.indentSize) & raw & "\n")

template indent*: untyped =
  context.indent += 1

template dedent*: untyped =
  context.indent -= 1

const C_TYPES = {"Int": "int", "Float": "float", "Bool": "bool"}.toTable()

proc genName*(node, context) =
  emit node.name

proc genInt*(node, context) =
  emit $node.i

proc genNumber*(node, context) =
  emit $node.i

proc genNew*(node, context) =
  if node[1].typ == Type(kind: TSimple, name: "Int"):
    emit "{int* tmp = malloc(sizeof(int));*tmp = "
    gen(node[1], context)
    emit "tmp;}"







# FREE


  
proc genFree*(node, context) =
  emit "free("
  gen(node[1], context)
  emit ")"

proc genDeref*(node, context) =
  emit "*"
  gen(node[1], context)
  
  
proc genCall*(node, context) =
  if node[0].kind == Name:
    if node[0].name == "new":
      genNew(node, context)
      return
    elif node[0].name == "free":
      genFree(node, context)
      return
    elif node[0].name == "deref":
      genDeref(node, context)
      return
  gen(node[0], context)
  emit "("
  for arg in node.children[1 .. ^1]:
    gen(arg, context)
    emit ","
  emit ")"

proc genDeclaration*(node, context) =
  # new gets the lastName for path
  # otherwise a = b makes a get b path
  genType node[1][1].typ, context
  gen node[1], context

proc genType*(typ: Type; context) =
  case typ.kind:
  of TSimple:
    emit C_TYPES[$typ.name]
  of TPointer:
    genType(typ.obj, context)
    emit "*"
  else:
    echo "what type"
    echo typ.repr
    quit(1)

proc genCode(node, context) =
  genChildren(node.children, context)

proc genProgram*(node, context) =
  for i, child in node.children:
    if child.isNil:
      continue
    echo child.kind
    gen(child, context)

proc gen*(node, context) =
  genCase(NodeKind.low, gen, node, context)

proc gen*(node, context; path: string) =
  gen(node, context)
  writeFile(path, context.topLevel.join("") & context.output.join(""))

proc genChildren*(nodes: seq[Node]; context) =
  for node in nodes:
    gen(node, context)


