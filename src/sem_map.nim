import types, macros, sequtils, strformat, strutils, algorithm, options, sugar, tables
proc check*(node: Node, env: TypeEnv)
proc checkChildren*(nodes: seq[Node], env: TypeEnv)

using
  node: Node
  env: TypeEnv

proc checkAccess(node, env; message: string)

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
        echo "NO ", node.kind
        for `child` in node.children:
          `childCall`

    result.add(nnkOfBranch.newTree(aNode, code))
  
proc check_module*(env; name: string) =
  var res = check(parse(readFile(name & ".js")), env)
  # => final ast ready for cgen
  # => also after we cache and also we have to merge those
  # inside our env: just try to it each time for now
proc checkImport*(node, env) =
  if env.root.imported.hasKey(node[0].name):
    discard
  else:
    # naive, but we just assume import is top level for now
    # and just parse + check it
    env.root.imported[node[0].name] = true
    env.root.check_module(node[0].name)
    for name, typ in env.imported[node[0].name]:


proc checkName*(node, env) =
  let t = env[node.name]
  if t.kind == TSimple and t.name.len == 0:
    # for name, typ in env.types:
    #   echo name, " ", typ.name
    echo &"NO {node.name}"
    quit(1)
  else:
    node.typ = t

proc checkInt*(node, env) =
  node.typ = env["Int"]

proc checkCall*(node, env) =
  if node[0].kind == Name:
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
  check(node[1][1], env)
  env[node[1][0].name] = node[1][1].typ

proc genType*(node, env): Type =
  Type(kind: TSimple, name: node.name)

proc checkFn*(node, env) =
  var t = Type(kind: TConcrete, name: "Function")
  var signature: Node
  var args: Node
  var code: Node
  var name: string
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
    # echo arg.name
  check(code, childEnv)
  
proc checkCode(node, env) =
  checkChildren(node.children, env)

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
