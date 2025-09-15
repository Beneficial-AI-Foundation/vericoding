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

def main : IO Unit := return ()