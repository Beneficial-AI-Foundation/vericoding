import Mathlib
-- <vc-preamble>
def R (n : Nat) : Nat :=
if n = 0 then
0
else if R (n-1) > n then
R (n-1) - n
else
R (n-1) + n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper to compute triangular numbers
def triangular (n : Nat) : Nat := n * (n + 1) / 2

-- LLM HELPER: Auxiliary function that matches R's structure exactly
def calcR_aux (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => 
    let prev := calcR_aux k
    if prev > k + 1 then prev - (k + 1) else prev + (k + 1)

-- LLM HELPER: Lemma showing calcR_aux equals R
lemma calcR_aux_eq_R (n : Nat) : calcR_aux n = R n :=
by
  induction n with
  | zero => 
    unfold calcR_aux R
    simp
  | succ k ih =>
    unfold calcR_aux R
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [ih]
    by_cases h : calcR_aux k > k + 1
    · simp [h]
    · simp [h]
-- </vc-helpers>

-- <vc-definitions>
def calcR (n : Nat) : Nat :=
match n with
| 0 => 0
| k + 1 => 
  let prev := calcR k
  if prev > k + 1 then prev - (k + 1) else prev + (k + 1)
-- </vc-definitions>

-- <vc-theorems>
theorem calcR_spec (n : Nat) : calcR n = R n :=
by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => 
      unfold calcR R
      simp
    | succ k =>
      unfold calcR R
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      have h_prev : calcR k = R k := by
        apply ih
        simp
      rw [h_prev]
      by_cases h : R k > k + 1
      · simp [h]
      · simp [h]
-- </vc-theorems>
