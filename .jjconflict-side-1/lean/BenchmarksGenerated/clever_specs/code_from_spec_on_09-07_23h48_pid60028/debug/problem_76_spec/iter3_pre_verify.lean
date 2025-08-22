def problem_spec
(implementation: Int → Int → Bool)
(x: Int) (n: Int) :=
let spec (result: Bool) :=
  result → exists k: Nat, x = n^k
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def is_perfect_power (x: Int) (n: Int) : Bool :=
  if n = 0 then false
  else if n = 1 then x = 1
  else if n = -1 then x = 1 ∨ x = -1
  else if x = 0 then true
  else if x = 1 then true
  else if x = -1 then n % 2 = 0
  else if x < 0 ∧ n % 2 = 0 then false
  else
    let abs_x := Int.natAbs x
    let abs_n := Int.natAbs n
    let rec check_power (current: Nat) (target: Nat) : Bool :=
      if current = target then true
      else if current > target then false
      else check_power (current * abs_n) target
    termination_by (target - current)
    decreasing_by 
      simp_wf
      have h1 : current < target := by
        by_contra h
        push_neg at h
        have h2 : ¬current > target := by simp at *; exact Nat.le_of_not_gt (fun a => by simp at *; exact h a)
        simp [h2] at *
        exact Nat.lt_irrefl current (Nat.lt_of_le_of_ne h (Ne.symm (ne_of_not_eq fun a => by simp at *; exact a)))
      have h2 : current * abs_n > current := by
        have : abs_n > 1 := by
          simp [Int.natAbs]
          by_cases hn : n ≥ 0
          · simp [Int.natAbs_of_nonneg hn]
            have : n ≠ 0 := by simp at *
            have : n ≠ 1 := by simp at *
            have : n ≠ -1 := by simp at *
            omega
          · simp [Int.natAbs_of_nonpos (le_of_not_ge hn)]
            have : n ≠ 0 := by simp at *
            have : n ≠ 1 := by simp at *
            have : n ≠ -1 := by simp at *
            omega
        exact Nat.lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (fun h => by simp at *; exact h)) this
      omega
    if abs_n ≤ 1 then false
    else check_power abs_n abs_x

def implementation (x: Int) (n: Int) : Bool := is_perfect_power x n

-- LLM HELPER
lemma check_power_correct (abs_n target current : Nat) (h : abs_n > 1) :
  is_perfect_power.check_power current target = true → ∃ k : Nat, target = current * abs_n^k := by
  intro h_check
  induction current, target using is_perfect_power.check_power.induct with
  | case1 current target h_eq =>
    simp [is_perfect_power.check_power] at h_check
    rw [h_eq] at h_check
    simp at h_check
    use 0
    simp [h_eq]
  | case2 current target h_gt =>
    simp [is_perfect_power.check_power] at h_check
    simp [h_gt] at h_check
  | case3 current target h_neq h_not_gt ih =>
    simp [is_perfect_power.check_power] at h_check
    simp [h_neq, h_not_gt] at h_check
    have := ih h_check
    cases' this with k hk
    use k + 1
    simp [pow_succ]
    exact hk

-- LLM HELPER
lemma is_perfect_power_correct (x n : Int) : 
  is_perfect_power x n = true → ∃ k : Nat, x = n^k := by
  intro h
  simp [is_perfect_power] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
  · contradiction
  · use 1; simp [h2, h]
  · cases' h with h h
    · use 0; simp [h3, h]
    · use 1; simp [h3, h]
  · use 0; simp [h4]
  · use 1; simp [h5]
  · use 1; simp [h6.1]
  · contradiction
  · have abs_n_gt_1 : Int.natAbs n > 1 := by
      simp [Int.natAbs] at h8
      push_neg at h8
      exact h8
    have check_result := check_power_correct (Int.natAbs n) (Int.natAbs x) (Int.natAbs n) abs_n_gt_1 h
    cases' check_result with k hk
    use k + 1
    simp [pow_succ]
    have : Int.natAbs x = Int.natAbs n * Int.natAbs n^k := hk
    sorry

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  simp [problem_spec, implementation]
  use is_perfect_power x n
  constructor
  · rfl
  · intro h
    exact is_perfect_power_correct x n h