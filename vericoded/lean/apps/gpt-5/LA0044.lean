import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  n ≥ 13 ∧ n % 2 = 1 ∧ s.length = n

def count_eights_in_prefix (s : String) (len : Nat) : Nat :=
  if len = 0 then 0
  else if len > s.length then 0
  else 
    let char_at_pos := s.get! ⟨len - 1⟩
    (if char_at_pos = '8' then 1 else 0) + count_eights_in_prefix s (len - 1)

instance (n : Int) (s : String) : Decidable (ValidInput n s) := by
  unfold ValidInput
  infer_instance

def VasyaWins (n : Int) (s : String) : Bool :=
  let petya_moves := (n - 11) / 2
  let prefix_len := n - 10
  let eights_in_prefix := count_eights_in_prefix s prefix_len.natAbs
  petya_moves < eights_in_prefix

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : String :=
  if VasyaWins n s then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : String) (h_precond : solve_precond n s) : Prop :=
  (result = "NO" ∨ result = "YES") ∧ 
  result = (if VasyaWins n s then "YES" else "NO")

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  by_cases hwin : VasyaWins n s
  · constructor
    · right; simp [solve, hwin]
    · simp [solve, hwin]
  · constructor
    · left; simp [solve, hwin]
    · simp [solve, hwin]
-- </vc-theorems>
