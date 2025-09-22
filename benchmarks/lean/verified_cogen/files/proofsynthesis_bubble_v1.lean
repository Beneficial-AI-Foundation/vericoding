-- <vc-preamble>
def test1_precond (nums : Array Nat) : Prop :=
  True

@[reducible, simp]
def sortedBetween (a : Array Nat) (fromIdx : Int) (toIdx : Int) : Prop :=
  ∀ i j : Int, fromIdx ≤ i ∧ i < j ∧ j < toIdx → a[i.toNat]! ≤ a[j.toNat]!

@[reducible, simp]
def isReorderOf (r : Array Int) (p : Array Nat) (s : Array Nat) : Prop :=
  r.size = s.size ∧ 
  (∀ i : Int, 0 ≤ i ∧ i < r.size → 0 ≤ r[i.toNat]! ∧ r[i.toNat]! < r.size) ∧
  (∀ i j : Int, 0 ≤ i ∧ i < j ∧ j < r.size → r[i.toNat]! ≠ r[j.toNat]!) ∧
  (∀ i : Int, 0 ≤ i ∧ i < r.size → p[i.toNat]! = s[r[i.toNat]!.toNat]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def test1 (nums : Array Nat) (h_precond : test1_precond nums) : Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def test1_postcond (nums : Array Nat) (result : Array Nat) (h_precond : test1_precond nums) : Prop :=
  sortedBetween result 0 result.size ∧ 
  ∃ r : Array Int, isReorderOf r result nums

theorem test1_spec_satisfied (nums : Array Nat) (h_precond : test1_precond nums) :
    test1_postcond nums (test1 nums h_precond) h_precond := by
  sorry
-- </vc-theorems>