import types, macros, sequtils, strformat, strutils, algorithm, options, sugar, tables, gara

proc check*(node: Node, env: TypeEnv)
proc checkChildren*(nodes: seq[Node], env: TypeEnv)



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
        # echo "=> ", node.kind
        `call`
      else:
        # echo "NO ", node.kind
        for `child` in node.children:
          `childCall`

    result.add(nnkOfBranch.newTree(aNode, code))


proc checkName*(node, env) =
  let t = env[node.name]
  if t.name.len == 0:
    # for name, typ in env.types:
    #   echo name, " ", typ.name
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
    # echo arg.name
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



using
  l: SyExpression
  r: SyExpression

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
    let l = exp.left.simplify
    let r = exp.right.simplify
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
      if l.kind == SyInt and l.i == 0 or r.kind == SyInt and r.i == 0:
        result = SyExpression(kind: SyInt, i: 0)
      elif l.kind == SyInt and l.i == 1:
        result = r
      elif r.kind == SyInt and r.i == 1:
        result = l
      elif l.kind == SyInt and r.kind == SyInt:
        result = SyExpression(kind: SyInt, i: l.i * r.i)
      elif l == r:
        result = SyExpression(kind: SyPower, left: l, right: 2)
      else:
        result = exp

  of SySum:
    let coefficient = (exp.finish.simplifyBasic - exp.start.simplifyBasic).simplifyBasic
    result = SyExpression(kind: SyMul, left: coefficient, right: exp.child.simplifyBasic)
  else:
    result = exp

proc simplify(exp: SyExpression): SyExpression =
  var current: SyExpression = nil
  var nextExp = exp
  while current != nextExp:
    current = nextExp
    nextExp = nextExp.simplifyBasic
  result = nextExp

proc b(node: Node): SyExpression =
  match node:
    Name(name: @name):
      SyExpression(kind: Symbol, name: name)
    Number(i: @i):
      SyExpression(kind: SyInt, i: i)
    ComplexityInfix(children: @[@left, @a, @right]):
      case a.name:
      of "*": SyExpression(kind: SyMul, left: b(left), right: b(right))
      of "^": SyExpression(kind: SyPower, left: b(left), right: b(right))
      of "+": SyExpression(kind: SyPlus, left: b(left), right: b(right))
      of "-": SyExpression(kind: SyMinus, left: b(left), right: b(right))
      else: nil
    BigO(children: @[@child]):
      b(child)
    _:
      nil

proc complexityFunctionDef*(node, cenv): SyExpression =
  echo node
  if node[0].kind != ComplexitySignature:
    return

  var childCenv = initComplexityEnv(@[cenv], nil)

  for i, arg in node[3].children:
    childCenv[arg.name] = SyExpression(kind: Symbol, name: node[0][i].name)
  var b2 = b(node[0][node[0].children.len - 1])
  let code = node[4]
  var exp = toSymbol(0)
  for child in code.children:
    let e2 = complexity(child, childCenv)
    exp = exp + e2
  echo text(exp)
  var res = simplify(exp)
  if b2 != res:
    echo "error: expected ", text(b2), " not ", text(res)
    quit(1)

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
  of Code:
    var sum: SyExpression = 0
    for child in node.children:
      sum = sum + complexity(child, cenv)
    sum
  else:
    1
  

proc complexityCheck*(node, cenv) =
  discard complexity(node, cenv)

  





