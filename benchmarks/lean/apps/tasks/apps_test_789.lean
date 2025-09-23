-- <vc-preamble>
def ValidLuckyNumber (n : String) : Prop :=
  n.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < n.length → n.get (String.Pos.mk i) = '4' ∨ n.get (String.Pos.mk i) = '7'

partial def convertToBinary (n : String) : String :=
  if n.length = 0 then ""
  else if n.get ⟨0⟩ = '4' then 
    "0" ++ convertToBinary (n.drop 1)
  else 
    "1" ++ convertToBinary (n.drop 1)

def pow2 : Nat → Nat
| 0 => 1
| n + 1 => 2 * pow2 n

partial def binaryToInt (s : String) : Nat :=
  if s.length = 0 then 0
  else if s.get ⟨0⟩ = '1' then 
    pow2 (s.length - 1) + binaryToInt (s.drop 1)
  else 
    binaryToInt (s.drop 1)

def ValidResult (n : String) (result : Int) : Prop :=
  ValidLuckyNumber n →
  (result > 0 ∧ result = 2 * (↑(pow2 (n.length - 1)) - 1) + ↑(binaryToInt (convertToBinary n)) + 1)

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