import os
import sem, npeg, parser, types, strutils, sequtils


var program = "hello.js"
var input = """
fn ok(a: *Int):
  free(a)

var a = new(0)
var b = a
ok(a)
free(b)

"""

var example = parse(input)

var env = newTypeEnv()
env["Int"] = Type(kind: TSimple, name: "Int")
env["Bool"] = Type(kind: TSimple, name: "Bool")
env["echo"] = Type(kind: TFunction, functionArgs: @[Type(kind: TAny)])

echo example
check(example, env)

# fn ok(a: *Int, b: *Int):
#   free(a)
#   echo(deref(b))

# var a = new(0)
# var b = new(1)

# ok(a, b)

# a = new(0)
# b = a

# ok(a, b)
