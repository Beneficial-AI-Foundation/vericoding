You probably know that the "mode" of a set of data is the data point that appears most frequently. Looking at the characters that make up the string `"sarsaparilla"` we can see that the letter `"a"` appears four times, more than any other letter, so the mode of `"sarsaparilla"` is `"a"`.

But do you know what happens when two or more data points occur the most? For example, what is the mode of the letters in `"tomato"`? Both `"t"` and `"o"` seem to be tied for appearing most frequently.

Turns out that a set of data can, in fact, have multiple modes, so `"tomato"` has two modes: `"t"` and `"o"`. It's important to note, though, that if *all* data appears the same number of times there is no mode. So `"cat"`, `"redder"`, and `[1, 2, 3, 4, 5]` do not have a mode.

Your job is to write a function `modes()` that will accept one argument `data` that is a sequence like a string or a list of numbers and return a sorted list containing the mode(s) of the input sequence. If data does not contain a mode you should return an empty list.

For example:

```python
>>> modes("tomato")
["o", "t"]
>>> modes([1, 3, 3, 7])
[3]
>>> modes(["redder"])
[]
```

You can trust that your input data will always be a sequence and will always contain orderable types (no inputs like `[1, 2, 2, "a", "b", "b"]`).

def count {α : Type} [BEq α] (x : α) (xs : List α) : Nat :=
  xs.filter (· == x) |>.length

/-- Test if list is sorted -/

def IsSorted {α : Type} [LE α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ IsSorted (y :: xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded