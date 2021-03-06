# Praise God !



import types, macros, sequtils, strformat, strutils, algorithm, options, sugar, tables, tools

proc check*(node: Node, env: TypeEnv)
proc checkChildren*(nodes: seq[Node], env: TypeEnv)

using
  node: Node
  env: TypeEnv

proc checkAccess(node, env; message: string)

proc checkName*(node, env) =
  let t = env[node.name]
  if t.isNil or t.kind == TSimple and t.name.len == 0:
    # for name, typ in env.types:
    #   echo name, " ", typ.name
    echo &"NO {node.name}"
    quit(1)
  else:
    node.typ = t

proc checkInt*(node, env) =
  node.typ = env["Int"]

proc checkNumber*(node, env) =
  node.typ = env["Int"]

proc unify(expected: Type, passed: Node; env) =
  if expected.kind != TAny and passed.typ != expected:
    echo "expected arg" #&"expected arg with {expected}, no {passed.typ}"
    quit(1)

proc checkNew*(node, env) =
  check(node[1], env)
  if node[1].typ == env["Int"]:
    node.typ = Type(kind: TPointer, obj: node[1].typ)
  else:
    return
  node.typ.path = path(@[env.lastName])
  env.paths[node.typ.path] = 1
  env.freed[node.typ.path] = false








# FREE


  
proc checkFree*(node, env) =
  check(node[1], env)
  if node[1].typ.kind != TPointer:
    echo "can't free type no pointer"
    quit(1)
  
  checkAccess(node[1], env, "free")

  env.paths[node[1].typ.path] -= 1
  env.freed[node[1].typ.path] = true
  node.typ = env["Void"]

proc checkDeref*(node, env) =
  check(node[1], env)
  if node[1].typ.kind != TPointer:
    echo "can't deref no pointer"
    quit(1)
  
  checkAccess(node[1], env, "deref")
  node.typ = node[1].typ.obj
  
proc checkAccess(node, env; message: string) =
  # free only if not freed
  if not env.paths.hasKey(node.typ.path):
    echo &"no path for {message}"
    quit(1)
  
  var freed = env.freed.getOrDefault(node.typ.path, false)
  if freed:
    echo &"can't {message}: freed"
    quit(1)
  
  
proc checkCall*(node, env) =
  if node[0].kind == Name:
    if node[0].name == "new":
      checkNew(node, env)
      return
    elif node[0].name == "free":
      checkFree(node, env)
      return
    elif node[0].name == "deref":
      checkDeref(node, env)
      return
  check(node[0], env)
  if node[0].typ.kind != TFunction:
    echo &"expected function {node[0]}"
    quit(1)
  if node[0].typ.functionArgs.len != node.children.len - 1:
    echo &"expected {node.children.len - 1} args, not {node[0].typ.functionArgs.len}"
    quit(1)

  for i in 0 ..< node.children.len - 1:
    let expected = node[0].typ.functionArgs[i]
    var passed = node[i + 1]
    check(passed, env)
    unify(expected, passed, env)

proc checkDeclaration*(node, env) =
  # new gets the lastName for path
  # otherwise a = b makes a get b path
  env.lastName = node[1][0].name
  check(node[1][1], env)
  env.lastName = ""
  env[node[1][0].name] = node[1][1].typ
  node.typ = env["Void"]

proc genType*(node, env): Type =
  case node.kind:
  of Name, Typename:
    Type(kind: TSimple, name: node.name)
  of PointerType:
    Type(kind: TPointer, obj: genType(node[0], env))
  else:
    echo "what type"
    echo node
    quit(1)

proc checkComplexitySignature*(node, env) =
  discard

proc checkFn*(node, env) =
  var t = Type(kind: TConcrete, name: "Function")
  for child in node[1].children: # args
    echo child
    t.params.add(genType(child[1], env))
  node.typ = t
  let existing = env[node[0].name]
  if not existing.isNil:
    echo &"Overriding {node[0].name}"
    quit(1)
  env[node[0].name] = t
  var childEnv = newTypeEnv()
  childEnv.previous = @[env]
  for i, arg in node[1].children:
    childEnv[arg[0].name] = t.params[i]
    echo arg[0].name
  check(node[2], childEnv)
  
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
  let l = node[0].typ
  let r = node[2].typ

  case node[1].name:
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
    if child.isNil:
      continue
    echo child.kind
    check(child, env)

proc check*(node, env) =
  genCase(NodeKind.low, check, node, env)

proc checkChildren*(nodes: seq[Node]; env) =
  for node in nodes:
    check(node, env)


