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

def main : IO Unit := return ()