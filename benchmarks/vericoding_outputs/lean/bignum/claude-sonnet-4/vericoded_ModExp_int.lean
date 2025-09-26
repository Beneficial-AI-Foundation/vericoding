import Mathlib
-- <vc-preamble>
namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)


-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Corrected lemma with proper induction
lemma exp_int_eq_pow (x y : Nat) : Exp_int x y = x ^ y := by
  induction y with
  | zero => 
    unfold Exp_int
    rfl
  | succ k ih => 
    unfold Exp_int
    rw [if_neg (Nat.succ_ne_zero k)]
    rw [Nat.succ_sub_one]
    rw [ih]
    rw [pow_succ]
    rw [mul_comm]
-- </vc-helpers>


-- <vc-definitions>
def ModExp_int (x y n z : Nat) : Nat :=
  if z ≤ 1 then 0
  else if y = 0 then 1 % z
  else (x ^ y) % z
-- </vc-definitions>

-- <vc-theorems>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
  unfold ModExp_int
  split
  · -- Case: z ≤ 1, but we have hz : z > 1
    have : z > 1 ∧ z ≤ 1 := ⟨hz, by assumption⟩
    have : ¬(z > 1 ∧ z ≤ 1) := by
      intro ⟨h1, h2⟩
      exact Nat.not_lt.mpr h2 h1
    contradiction
  · split
    · -- Case: y = 0
      have h_y_eq : y = 0 := by assumption
      rw [h_y_eq]
      rw [exp_int_eq_pow]
      rw [pow_zero]
    · -- Case: y ≠ 0
      rw [exp_int_eq_pow]
-- </vc-theorems>

