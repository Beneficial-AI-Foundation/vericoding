import Mathlib
-- <vc-preamble>
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']
partial def FilterVowels (xs : Array Char) : Array Char :=
if xs.size = 0 then
#[]
else if vowels.contains (xs[xs.size - 1]!) then
FilterVowels (xs.extract 0 (xs.size - 1)) |>.push (xs[xs.size - 1]!)
else
FilterVowels (xs.extract 0 (xs.size - 1))
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Since FilterVowels is already defined and we need to match its behavior exactly,
-- we can use it directly or provide an equivalent implementation
-- </vc-helpers>

-- <vc-definitions>
def FilterVowelsArray (xs : Array Char) : Array Char :=
FilterVowels xs
-- </vc-definitions>

-- <vc-theorems>
theorem FilterVowelsArray_spec (xs : Array Char) (ys : Array Char) :
ys = FilterVowelsArray xs →
FilterVowels xs = ys :=
by
  intro h
  rw [h]
  rfl
-- </vc-theorems>
