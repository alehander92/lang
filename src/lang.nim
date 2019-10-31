import os
import sem, gen, parser, types, strutils, sequtils


var program = "hello.js"
# fn ok(a: *Int):
#   free(a)


var input = """
var a = new(0)
var b = a
free(a)
# free(b)
"""

var example = parse(input)

var env = newTypeEnv()
env["Int"] = Type(kind: TSimple, name: "Int")
env["Bool"] = Type(kind: TSimple, name: "Bool")
env["echo"] = Type(kind: TFunction, functionArgs: @[Type(kind: TAny)])

var cGenerator = CGenerator(indentSize: 4)

echo example
check(example, env)

gen(example, cGenerator, "hello.c")

# echo "*stopped,reason=\"signal-received\",signal-name=\"SIGSEGV\",signal-meaning=\"Segmentation fault\",frame={addr=\"0x0\",func=\"a\",args=[],arch=\"i386:x86-64\"},thread-id=\"1\",stopped-threads=\"all\"\n\n(gdb)\n"

# fn ok(a: *Int, b: *Int):
#   free(a)
#   echo(deref(b))

# var a = new(0)
# var b = new(1)

# ok(a, b)

# a = new(0)
# b = a

# ok(a, b)
