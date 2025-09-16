-- <vc-preamble>

def ValidLuckyNumber (n : String) : Prop :=
  n.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < n.length → n.data[i]! = '4' ∨ n.data[i]! = '7'

def convertToBinary (n : String) : String :=
  sorry

def pow2 (n : Nat) : Nat :=
  if n = 0 then 1 else 2 * pow2 (n - 1)

def binaryToInt (s : String) : Nat :=
  sorry

def ValidResult (n : String) (result : Int) : Prop :=
  result > 0 ∧ result = 2 * (Int.ofNat (pow2 (n.length - 1)) - 1) + Int.ofNat (binaryToInt (convertToBinary n)) + 1

@[reducible, simp]
def solve_precond (n : String) : Prop :=
  ValidLuckyNumber n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : String) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : String) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidResult n result

theorem solve_spec_satisfied (n : String) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>
