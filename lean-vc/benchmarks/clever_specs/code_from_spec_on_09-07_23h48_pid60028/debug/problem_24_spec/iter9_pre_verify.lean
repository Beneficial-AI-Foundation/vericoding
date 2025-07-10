def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
0 < n → 0 < result → result ∣ n → ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def largest_proper_divisor (n: Nat) : Nat :=
if n ≤ 1 then 1
else
  let rec find_largest (k: Nat) : Nat :=
    if k = 1 then 1
    else if n % k = 0 then k
    else find_largest (k - 1)
  termination_by k
  decreasing_by {
    simp_wf
    exact Nat.pred_lt (Ne.symm (Nat.ne_of_gt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_not_ge (fun h => by simp [Nat.le_one_iff_eq_zero_or_eq_one] at h; cases h with | inl h => simp [h] | inr h => simp [h]))))))
  }
  find_largest (n - 1)

def implementation (n: Nat) : Nat := largest_proper_divisor n

-- LLM HELPER
lemma largest_proper_divisor_pos (n: Nat) : 0 < largest_proper_divisor n := by
  unfold largest_proper_divisor
  split
  · simp
  · simp only [largest_proper_divisor.find_largest]
    generalize h : n - 1 = k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      simp [largest_proper_divisor.find_largest]
      split
      · simp
      · split
        · simp
        · apply ih
          omega

-- LLM HELPER
lemma find_largest_divides (n k: Nat) (h: 0 < n) (hk: k < n) : 
  largest_proper_divisor.find_largest n k ∣ n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    simp [largest_proper_divisor.find_largest]
    split
    · simp
    · split
      · simp [Nat.dvd_iff_mod_eq_zero]
        assumption
      · apply ih (k - 1) (by omega)
        exact h
        omega

-- LLM HELPER
lemma largest_proper_divisor_divides (n: Nat) (h: 0 < n) : largest_proper_divisor n ∣ n := by
  unfold largest_proper_divisor
  split
  · simp at h
  · apply find_largest_divides n (n - 1) h
    omega

-- LLM HELPER
lemma find_largest_maximal (n k: Nat) (h: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ k → x ≤ largest_proper_divisor.find_largest n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intros x hx_div hx_ne hx_le
    simp [largest_proper_divisor.find_largest]
    split
    · simp at hx_le
      exact hx_le
    · split
      · exact hx_le
      · apply ih (k - 1) (by omega) x hx_div hx_ne
        omega

-- LLM HELPER
lemma largest_proper_divisor_maximal (n: Nat) (h: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ largest_proper_divisor n := by
  intros x hx_div hx_ne
  unfold largest_proper_divisor
  split
  · simp at h
  · apply find_largest_maximal n (n - 1) h x hx_div hx_ne
    have : x < n := by
      by_contra h_not
      push_neg at h_not
      have : x = n := by
        apply Nat.eq_of_le_of_dvd h_not hx_div h
      exact hx_ne this
    omega

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use largest_proper_divisor n
  constructor
  · rfl
  · intro h_pos
    constructor
    · exact largest_proper_divisor_pos n
    · constructor
      · exact largest_proper_divisor_divides n h_pos
      · exact largest_proper_divisor_maximal n h_pos