import Mathlib
-- <vc-preamble>
def f2 (n : Nat) : Nat :=
if n = 0 then 0
else 5 * f2 (n / 3) + n % 4
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def f2_tailrec_aux (m p acc : Nat) : Nat :=
  if m = 0 then acc
  else f2_tailrec_aux (m / 3) (p * 5) (acc + (m % 4) * p)
termination_by m

-- LLM HELPER
theorem f2_tailrec_aux_correct (m : Nat) : ∀ p acc, f2_tailrec_aux m p acc = f2 m * p + acc := by
  induction m using Nat.strongRecOn with
  | ind m IH =>
    intros p acc
    unfold f2_tailrec_aux f2
    split_ifs with h_m
    · simp
    · have h_lt : m / 3 < m := Nat.div_lt_self (Nat.pos_of_ne_zero h_m) (by norm_num)
      rw [IH (m / 3) h_lt]
      ring

-- </vc-helpers>

-- <vc-definitions>
def mod2 (n : Nat) : Nat :=
f2_tailrec_aux n 1 0
-- </vc-definitions>

-- <vc-theorems>
theorem mod2_spec (n : Nat) : mod2 n = f2 n :=
by
  unfold mod2
  rw [f2_tailrec_aux_correct]
  simp
-- </vc-theorems>
