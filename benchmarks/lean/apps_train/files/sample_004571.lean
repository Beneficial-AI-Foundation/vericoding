Your task is to find all the elements of an array that are non consecutive.

A number is non consecutive if it is not exactly one larger than the previous element in the array. The first element gets a pass and is never considered non consecutive.

~~~if:javascript,haskell,swift
Create a function named `allNonConsecutive`
~~~
~~~if:python,rust
Create a function name `all_non_consecutive`
~~~

E.g., if we have an array `[1,2,3,4,6,7,8,15,16]` then `6` and `15` are non-consecutive.

~~~if:javascript,python
You should return the results as an array of objects with two values `i: ` and `n: `.
~~~
~~~if:haskell,swift,rust
You should return the results as an array of tuples with two values: the index of the non-consecutive number and the non-consecutive number.
~~~

E.g., for the above array the result should be:
```python
[
  {'i': 4, 'n': 6},
  {'i': 7, 'n': 15}
]
```

If the whole array is consecutive or has one element then return an empty array.

The array elements will all be numbers. The numbers will also all be unique and in ascending order. The numbers could be positive and/or negetive and the gap could be larger than one.

If you like this kata, maybe try this one next: https://www.codewars.com/kata/represent-array-of-numbers-as-ranges

def List.Sorted {α : Type} (r : α → α → Prop) (l : List α) : Prop :=
  ∀ i j, i < j → j < l.length → r (l.get ⟨i, sorry⟩) (l.get ⟨j, sorry⟩)

structure Result where
  i : Nat
  n : Int

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
