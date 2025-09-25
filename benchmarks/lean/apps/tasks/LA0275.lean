-- <vc-preamble>
def XorRange (arr : List UInt32) (i j : Int) : UInt32 :=
  if i > j ∨ i < 0 ∨ j >= arr.length then 0
  else arr.drop i.natAbs |>.take ((j - i + 1).natAbs) |>.foldl (· ^^^ ·) 0

def ValidInput (arr : List UInt32) : Prop :=
  arr.length > 0

def IsMaxXorSubarray (arr : List UInt32) (result : UInt32) : Prop :=
  ValidInput arr →
  (∃ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.length ∧ result = XorRange arr i j ∧
   ∀ i1 j1, 0 ≤ i1 ∧ i1 ≤ j1 ∧ j1 < arr.length → 
     (XorRange arr i1 j1).toNat ≤ result.toNat)

@[reducible, simp]
def solve_precond (arr : List UInt32) : Prop :=
  ValidInput arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List UInt32) (h_precond : solve_precond arr) : UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (arr : List UInt32) (result : UInt32) (h_precond : solve_precond arr) : Prop :=
  IsMaxXorSubarray arr result

theorem solve_spec_satisfied (arr : List UInt32) (h_precond : solve_precond arr) :
    solve_postcond arr (solve arr h_precond) h_precond := by
  sorry
-- </vc-theorems>