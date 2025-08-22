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
    if abs_n ≤ 1 then false
    else
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
          have h2 : ¬current > target := by 
            simp at *
            omega
          omega
        have h2 : current * abs_n > current := by
          have : abs_n > 1 := by
            simp [Int.natAbs]
            by_cases hn : n ≥ 0
            · simp [Int.natAbs_of_nonneg hn]
              omega
            · simp [Int.natAbs_of_nonpos (le_of_not_ge hn)]
              omega
          exact Nat.lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (fun h => by omega)) this
        have : target - current * abs_n < target - current := by
          have : current < target := h1
          have : current * abs_n > current := h2
          have : current * abs_n ≤ target := by
            by_contra h_contra
            push_neg at h_contra
            have : current * abs_n > target := h_contra
            have : current > target := by
              have : current < current * abs_n := h2
              exact Nat.lt_trans this h_contra
            omega
          exact Nat.sub_lt_sub_left h1 this
        exact this
      check_power abs_n abs_x

def implementation (x: Int) (n: Int) : Bool := is_perfect_power x n

-- LLM HELPER
lemma is_perfect_power_correct (x n : Int) : 
  is_perfect_power x n = true → ∃ k : Nat, x = n^k := by
  intro h
  simp [is_perfect_power] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
  · contradiction
  · use 1; simp [h2]
  · cases' h with h_case h_case
    · use 0; simp [h3, h_case]
    · use 1; simp [h3, h_case]
  · use 0; simp [h4]
  · use 1; simp [h5]
  · use 1; simp [h6.1, h6.2]
  · contradiction
  · contradiction
  · use 1; simp

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  simp [problem_spec, implementation]
  use is_perfect_power x n
  constructor
  · rfl
  · intro h
    exact is_perfect_power_correct x n h