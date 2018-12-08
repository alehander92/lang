# good
import os
import lang, parser, types, strutils, sequtils


var program = paramStr(1)
var input = readFile(program)
var example0 = parse(input)

var env = newTypeEnv()
env["Int"] = Type(kind: TSimple, name: "Int")
env["String"] = Type(kind: TSimple, name: "String")
env["Bool"] = Type(kind: TSimple, name: "Bool")

var cenv = initComplexityEnv(@[], env)

check(example0, env)
complexityCheck(example0, cenv)

