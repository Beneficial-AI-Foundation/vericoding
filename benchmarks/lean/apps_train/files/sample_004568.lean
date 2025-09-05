__Function composition__ is a mathematical operation that mainly presents itself in lambda calculus and computability. It is explained well [here](http://www.mathsisfun.com/sets/functions-composition.html), but this is my explanation, in simple mathematical notation:

```
f3 = compose( f1 f2 )
   Is equivalent to...
f3(a) = f1( f2( a ) )
```

Your task is to create a `compose` function to carry out this task, which will be passed two functions or lambdas. Ruby functions will be passed, and should return, either a proc or a lambda. Remember that the resulting composed function may be passed multiple arguments!

```python
compose(f , g)(x)
=> f( g( x ) )
```

This kata is not available in haskell; that would be too easy!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
