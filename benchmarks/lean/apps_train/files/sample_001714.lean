/-
[Currying and partial application](http://www.2ality.com/2011/09/currying-vs-part-eval.html) are two ways of transforming a function into another function with a generally smaller arity. While they are often confused with each other, they work differently. The goal is to learn to differentiate them.

## Currying

> Is the technique of transforming a function that takes multiple arguments in such a way that it can be called as a chain of functions each with a single argument.

Currying takes a function:

```
f: X × Y → R
```

and turns it into a function:

```
f': X → (Y → R)
```

Instead of calling `f` with two arguments, we invoke `f'` with the first argument. The result is a function that we then call with the second argument to produce the result. Thus, if the uncurried `f` is invoked as:

```
f(3, 5)
```

then the curried `f'` is invoked as:

`f'(3)(5)`

### Example

Given this function:

```python
def add(x, y, z):
  return x + y + z
```

We can call in a normal way:

```python
add(1, 2, 3) # => 6
```

But we can create a curried version of `add(a, b, c)`function:

```python
curriedAdd = lambda a: (lambda b: (lambda c: add(a,b,c)))
curriedAdd(1)(2)(3) # => 6
```

## Partial application

> Is the process of fixing a number of arguments to a function, producing another function of smaller arity.

Partial application takes a function:

```
f: X × Y → R
```

and a fixed value `x` for the first argument to produce a new function

```
f': Y → R
```

`f'` does the same as `f`, but only has to fill in the second parameter which is why its arity is one less than the arity of `f`. One says that the first argument is bound to `x`.

### Example

```python
partialAdd = lambda a: (lambda *args: add(a,*args))
partialAdd(1)(2, 3) # => 6
```

-------------

Your work is to implement a generic `curryPartial()` function allows either currying or partial application.

For example:

```python
curriedAdd = curryPartial(add)
curriedAdd(1)(2)(3) # => 6

partialAdd = curryPartial(add, 1)
partialAdd(2, 3) # => 6
```

We want the function be very flexible.

All these examples should produce the same result:

```python
curryPartial(add)(1)(2)(3) # =>6 
curryPartial(add, 1)(2)(3) # =>6 
curryPartial(add, 1)(2, 3) # =>6 
curryPartial(add, 1, 2)(3) # =>6 
curryPartial(add, 1, 2, 3) # =>6 
curryPartial(add)(1, 2, 3) # =>6 
curryPartial(add)(1, 2)(3) # =>6 
curryPartial(add)()(1, 2, 3) # =>6 
curryPartial(add)()(1)()()(2)(3) # =>6 

curryPartial(add)()(1)()()(2)(3, 4, 5, 6) # =>6 
curryPartial(add, 1)(2, 3, 4, 5) # =>6 
```

And also all of these:

```python
curryPartial(curryPartial(curryPartial(add, 1), 2), 3) # =>6
curryPartial(curryPartial(add, 1, 2), 3) # =>6
curryPartial(curryPartial(add, 1), 2, 3) # =>6
curryPartial(curryPartial(add, 1), 2)(3) # =>6
curryPartial(curryPartial(add, 1)(2), 3) # =>6
curryPartial(curryPartial(curryPartial(add, 1)), 2, 3) # =>6
```
-/

def add2 (x y : Int) : Int :=
  sorry

def add3 (x y z : Int) : Int :=
  sorry

def concat3 (x y z : α) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def curry_partial : ((α → β) → (α → β)) :=
  sorry

theorem curry_preserves_binary_function (x y : Int) :
  curry_partial add2 x y = add2 x y :=
  sorry

theorem curry_preserves_ternary_function (x y z : Int) :
  curry_partial add3 x y z = add3 x y z :=
  sorry

theorem partial_application_preserves_result_1 (x y z : Int) :
  curry_partial add3 x y z = add3 x y z :=
  sorry

theorem partial_application_preserves_result_2 (x y z : Int) :
  curry_partial (curry_partial add3 x) y z = add3 x y z :=
  sorry

theorem nested_curry_calls (x y z : Int) :
  curry_partial (curry_partial (curry_partial add3 x) y) z = add3 x y z :=
  sorry

theorem curry_works_with_different_types {α : Type} (x y z : α) :
  curry_partial concat3 x y z = concat3 x y z :=
  sorry

end CurryPartial

-- Apps difficulty: interview
-- Assurance level: unguarded