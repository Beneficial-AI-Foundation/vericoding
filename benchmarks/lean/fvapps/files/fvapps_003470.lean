-- <vc-preamble>
def Digit := Nat
def NumStr := List Digit

instance : OfNat Digit n where
  ofNat := n

instance : LE Digit where
  le := Nat.le
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def series_slices (digits : NumStr) (n : Nat) : List (List Digit) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slice_length_bounds 
  (digits : NumStr) (n : Nat) (h : n > 0) :
  (n > digits.length → (series_slices digits n).isEmpty) ∧ 
  (n ≤ digits.length → 
    ((series_slices digits n).length = digits.length - n + 1) ∧
    (∀ slice ∈ series_slices digits n, slice.length = n)) :=
  sorry

theorem slice_contents
  (digits : NumStr) (n : Nat) (h₁ : n > 0) (h₂ : n ≤ digits.length) :
  ∀ i, i < (series_slices digits n).length →
    (series_slices digits n)[i]! = digits.take (n) :=
  sorry

theorem full_slice
  (digits : NumStr) (h : digits.length > 0) :
  let n := digits.length
  (series_slices digits n).length = 1 ∧
  (series_slices digits n)[0]! = digits :=
  sorry

theorem all_integers
  (digits : NumStr) (n : Nat) (h₁ : n > 0) (h₂ : n ≤ digits.length) :
  ∀ slice ∈ series_slices digits n,
    ∀ d ∈ slice, d ≤ 9 :=
  sorry
-- </vc-theorems>