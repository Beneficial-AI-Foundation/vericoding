Very simple, given a number, find its opposite.

Examples:
```
1: -1
14: -14
-34: 34
```

~~~if:sql
You will be given a table: `opposite`, with a column: `number`. Return a table with a column: `res`.
~~~

def opposite (x : Int) : Int := sorry

theorem double_negative_int (x : Int) :
  opposite (opposite x) = x := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
