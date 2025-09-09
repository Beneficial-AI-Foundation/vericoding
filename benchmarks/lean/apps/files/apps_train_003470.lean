def Digit := Nat
def NumStr := List Digit

instance : OfNat Digit n where
  ofNat := n

instance : LE Digit where
  le := Nat.le

-- <vc-helpers>
-- </vc-helpers>

def series_slices (digits : NumStr) (n : Nat) : List (List Digit) :=
  sorry

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

/-
info: [[0, 1], [1, 2], [2, 3], [3, 4]]
-/
-- #guard_msgs in
-- #eval series_slices "01234" 2

/-
info: [[0, 1, 2, 3], [1, 2, 3, 4]]
-/
-- #guard_msgs in
-- #eval series_slices "01234" 4

/-
info: [[0, 1, 2, 3, 4]]
-/
-- #guard_msgs in
-- #eval series_slices "01234" 5

-- Apps difficulty: introductory
-- Assurance level: guarded