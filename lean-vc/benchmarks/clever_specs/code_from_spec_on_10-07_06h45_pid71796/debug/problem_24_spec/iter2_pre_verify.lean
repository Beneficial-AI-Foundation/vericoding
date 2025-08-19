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
  let rec find_divisor (k: Nat) : Nat :=
    if k = 1 then 1
    else if n % k = 0 then k
    else find_divisor (k - 1)
  find_divisor (n - 1)

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
lemma largest_proper_divisor_divides (n: Nat) (h: 0 < n) : largest_proper_divisor n ∣ n := by
  unfold largest_proper_divisor
  split_ifs with h1
  · cases' h1 with h1 h1
    · have : n = 0 := by linarith
      rw [this] at h
      exact absurd h (by norm_num)
    · rw [h1]
      exact Nat.one_dvd n
  · have h2 : n > 1 := by linarith [h1]
    simp only [largest_proper_divisor]
    have find_div_spec : ∀ k, k ≤ n - 1 → k ≥ 1 → 
      (largest_proper_divisor.find_divisor n k) ∣ n := by
      intro k hk hk_pos
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        unfold largest_proper_divisor.find_divisor
        split_ifs with hk1 hkn
        · exact Nat.one_dvd n
        · rw [mod_eq_zero_iff_dvd] at hkn
          exact hkn
        · have : k > 1 := by linarith [hk1]
          apply ih (k - 1)
          · linarith
          · linarith
          · linarith
    apply find_div_spec (n - 1)
    · le_refl
    · linarith [h2]

-- LLM HELPER
lemma largest_proper_divisor_maximal (n: Nat) (h: 0 < n) : 
  ∀ x, x ∣ n → x ≠ n → x ≤ largest_proper_divisor n := by
  intro x hx hxn
  unfold largest_proper_divisor
  split_ifs with h1
  · cases' h1 with h1 h1
    · have : n = 0 := by linarith
      rw [this] at h
      exact absurd h (by norm_num)
    · rw [h1] at hx hxn
      have : x = 1 := by
        have : x ∣ 1 := hx
        exact Nat.eq_one_of_dvd_one this
      rw [this]
      norm_num
  · have h2 : n > 1 := by linarith [h1]
    have hx_bound : x < n := by
      have : x ∣ n := hx
      have : x ≠ n := hxn
      exact Nat.lt_of_dvd_of_ne h this this
    have find_div_maximal : ∀ k, k ≤ n - 1 → k ≥ 1 → 
      ∀ y, y ∣ n → y ≠ n → y ≤ k → y ≤ (largest_proper_divisor.find_divisor n k) := by
      intro k hk hk_pos y hy hyn hyk
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        unfold largest_proper_divisor.find_divisor
        split_ifs with hk1 hkn
        · have : y = 1 := by
          have : y ≤ 1 := by linarith [hk1, hyk]
          have : y ≥ 1 := by
            have : y > 0 := Nat.pos_of_dvd_of_pos hy h
            exact this
          linarith
          rw [this]
          norm_num
        · have : y ≤ k := hyk
          exact this
        · apply ih (k - 1)
          · linarith
          · linarith
          · linarith
          · exact hy
          · exact hyn
          · linarith [hyk]
    apply find_div_maximal (n - 1)
    · le_refl
    · linarith [h2]
    · exact hx
    · exact hxn
    · linarith [hx_bound]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
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