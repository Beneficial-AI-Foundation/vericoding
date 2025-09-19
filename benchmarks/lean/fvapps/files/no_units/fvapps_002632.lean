-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myCompare (a b : String) : String := sorry 
def specificity (s : String) : Nat × Nat × Nat := sorry

instance : LT (Nat × Nat × Nat) where
  lt x y := x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))
-- </vc-definitions>

-- <vc-theorems>
theorem compare_returns_input (a b : String) :
  let res := myCompare a b;
  (res = a ∨ res = b) := sorry

theorem compare_reflexive (s : String) :
  myCompare s s = s := sorry

theorem specificity_ordering (a b : String) :
  myCompare a b = a → 
  ¬(specificity a < specificity b) := sorry

theorem id_beats_class : 
  (specificity "#x").1 > (specificity ".x").1 := sorry

theorem class_beats_tag :
  (specificity ".x").2.1 > (specificity "x").2.1 := sorry

theorem specificity_output_format (s : String) :
  let spec := specificity s;
  spec.1 ≥ 0 ∧ spec.2.1 ≥ 0 ∧ spec.2.2 ≥ 0 := sorry
-- </vc-theorems>