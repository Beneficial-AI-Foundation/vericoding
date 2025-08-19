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
  let rec find_divisor (n: Nat) (k: Nat) : Nat :=
    if k = 1 then 1
    else if n % k = 0 then k
    else find_divisor n (k - 1)
  termination_by k
  decreasing_by simp_wf; omega
  find_divisor n (n - 1)

def implementation (n: Nat) : Nat := largest_proper_divisor n

-- LLM HELPER
lemma largest_proper_divisor_pos (n: Nat) : 0 < largest_proper_divisor n := by
  unfold largest_proper_divisor
  split_ifs with h
  · norm_num
  · simp only [largest_proper_divisor]
    have : 0 < 1 := by norm_num
    exact this

-- LLM HELPER
lemma mod_eq_zero_iff_dvd (a b : Nat) : a % b = 0 ↔ b ∣ a := by
  constructor
  · intro h
    exact Nat.dvd_iff_mod_eq_zero.mpr h
  · intro h
    exact Nat.dvd_iff_mod_eq_zero.mp h

-- LLM HELPER
lemma find_divisor_divides (n k : Nat) (h: 0 < n) (hk: k ≤ n - 1) : 
  largest_proper_divisor.find_divisor n k ∣ n := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    unfold largest_proper_divisor.find_divisor
    split_ifs with hk1 hkn
    · exact Nat.one_dvd n
    · rw [mod_eq_zero_iff_dvd] at hkn
      exact hkn
    · apply ih (k - 1)
      · omega
      · omega

-- LLM HELPER
lemma largest_proper_divisor_divides (n: Nat) (h: 0 < n) : largest_proper_divisor n ∣ n := by
  unfold largest_proper_divisor
  split_ifs with h1
  · exact Nat.one_dvd n
  · have h2 : n > 1 := by omega
    apply find_divisor_divides n (n - 1) h
    le_refl

-- LLM HELPER
lemma find_divisor_maximal (n k : Nat) (h: 0 < n) (hk: k ≤ n - 1) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ k → x ≤ largest_proper_divisor.find_divisor n k := by
  intro x hx hxn hxk
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    unfold largest_proper_divisor.find_divisor
    split_ifs with hk1 hkn
    · have : x ≤ 1 := by omega
      omega
    · exact hxk
    · apply ih (k - 1)
      · omega
      · omega
      · exact hx
      · exact hxn
      · omega

-- LLM HELPER
lemma largest_proper_divisor_maximal (n: Nat) (h: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ largest_proper_divisor n := by
  intro x hx hxn
  unfold largest_proper_divisor
  split_ifs with h1
  · have : x = 1 := by
      cases' h1 with h1 h1
      · omega
      · rw [h1] at hx hxn
        exact Nat.eq_one_of_dvd_one hx
    rw [this]
    norm_num
  · have h2 : n > 1 := by omega
    have hx_bound : x < n := Nat.lt_of_dvd_of_ne h hx hxn
    apply find_divisor_maximal n (n - 1) h
    · le_refl
    · exact hx
    · exact hxn
    · omega

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use largest_proper_divisor n
  constructor
  · rfl
  · intro h_pos
    intro h_result_pos
    intro h_divides
    exact largest_proper_divisor_maximal n h_pos