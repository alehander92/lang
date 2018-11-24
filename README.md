# pseudo-lang

```nim
Int -> Int
def fib(a):
  if a < 2:
    1
  else:
    fib(a - 1) + fib(a - 2)

echo(fib(0))
```


```nim
n -> O[n^2] M[1]
@progress
Int -> Int
def example1(n):
  var result = 0
  for i in 0 ..< n:
    for j in i ..< n:
      result += j
    saveProgress()
  return result
```

* type safety
* effects(inspired mostly by Nim)

```nim
effect @progress

trust @progress
trust O[1]
def saveProgress:
  ..
```

We have two kinds of properties: in primitives we can tell pseudo to trust us, so it uses them as axioms , otherwise we implicitly ask it to prove them.

In this case `@progress` and `O[1]` are assumed to be true and then checked in example1 .

* complexity 

Probably not going to be very sound, but maybe we can deal with some situations

Effects can be also functions: in this case they take a parameter and return a tag. 
We have compile time evaluation based on our interpreter.
