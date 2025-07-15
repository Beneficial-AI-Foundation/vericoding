-- LLM HELPER
def fibonacci_non_computable : Nat → Nat → Prop
| 0, result => result = 0
| 1, result => result = 1
| n + 2, result => ∃ f_n f_n_plus_1, 
    fibonacci_non_computable n f_n ∧ 
    fibonacci_non_computable (n + 1) f_n_plus_1 ∧ 
    result = f_n + f_n_plus_1

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
fibonacci_non_computable n result
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Nat) : Nat := 
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => implementation n + implementation (n + 1)

-- LLM HELPER
theorem fibonacci_non_computable_unique (n: Nat) (r1 r2: Nat) : 
  fibonacci_non_computable n r1 → fibonacci_non_computable n r2 → r1 = r2 := by
  intro h1 h2
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => 
      cases h1; cases h2; rfl
    | succ n' =>
      cases n' with
      | zero =>
        cases h1; cases h2; rfl
      | succ n'' =>
        cases h1 with
        | mk f_n1 h1_rest =>
          cases h1_rest with
          | mk f_n_plus_1_1 h1_final =>
            cases h1_final with
            | mk h1_n h1_rest2 =>
              cases h1_rest2 with
              | mk h1_n_plus_1 h1_eq =>
                cases h2 with
                | mk f_n2 h2_rest =>
                  cases h2_rest with
                  | mk f_n_plus_1_2 h2_final =>
                    cases h2_final with
                    | mk h2_n h2_rest2 =>
                      cases h2_rest2 with
                      | mk h2_n_plus_1 h2_eq =>
                        have eq_n : f_n1 = f_n2 := ih n'' (by simp [Nat.lt_add_two]) h1_n h2_n
                        have eq_n_plus_1 : f_n_plus_1_1 = f_n_plus_1_2 := ih (n'' + 1) (by simp [Nat.lt_add_one]) h1_n_plus_1 h2_n_plus_1
                        rw [h1_eq, h2_eq, eq_n, eq_n_plus_1]

-- LLM HELPER
theorem implementation_satisfies_spec (n: Nat) : 
  fibonacci_non_computable n (implementation n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => 
      simp [implementation, fibonacci_non_computable]
    | succ n' =>
      cases n' with
      | zero =>
        simp [implementation, fibonacci_non_computable]
      | succ n'' =>
        simp [implementation, fibonacci_non_computable]
        use implementation n'', implementation (n'' + 1)
        constructor
        · exact ih n'' (by simp [Nat.lt_add_two])
        constructor
        · exact ih (n'' + 1) (by simp [Nat.lt_add_one])
        · rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · exact implementation_satisfies_spec n