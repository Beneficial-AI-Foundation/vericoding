-- <vc-preamble>
def sortedBetween (a : Array Nat) (from_val to_val : Int) : Prop :=
  ∀ i j : Int, from_val ≤ i ∧ i < j ∧ j < to_val → a[i.toNat]! ≤ a[j.toNat]!

def isReorderOf (r : Array Int) (p s : Array Nat) : Prop :=
  r.size = s.size ∧ 
  (∀ i : Int, 0 ≤ i ∧ i < r.size → 0 ≤ r[i.toNat]! ∧ r[i.toNat]! < r.size) ∧
  (∀ i j : Int, 0 ≤ i ∧ i < j ∧ j < r.size → r[i.toNat]! ≠ r[j.toNat]!) ∧
  (∀ i : Int, 0 ≤ i ∧ i < r.size → p[i.toNat]! = s[r[i.toNat]!.toNat]!)

@[reducible, simp]
def test1_precond (nums : Array Nat) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def test1 (nums : Array Nat) (h_precond : test1_precond nums) : Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def test1_postcond (nums : Array Nat) (old_nums : Array Nat) (h_precond : test1_precond nums) : Prop :=
  sortedBetween nums 0 nums.size ∧ 
  ∃ r : Array Int, isReorderOf r nums old_nums

theorem test1_spec_satisfied (nums : Array Nat) (old_nums : Array Nat) (h_precond : test1_precond nums) :
    test1_postcond (test1 nums h_precond) old_nums h_precond := by
  sorry
-- </vc-theorems>