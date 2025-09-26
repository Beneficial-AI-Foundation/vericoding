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
-- no helpers needed
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
  simpa [FilterVowelsArray] using h.symm
-- </vc-theorems>
