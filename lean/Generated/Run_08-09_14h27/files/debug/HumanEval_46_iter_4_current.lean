import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: fibonacci_non_computable_4
use: |
  Non-computable definition to check if a number is a Fibonacci number such that
  fib(n) = fib(n - 1) + fib(n - 2) + fib(n - 3) + fib(n - 4).
problems:
  - 46
-/
inductive fibonacci_non_computable_4 : ℕ → ℕ → Prop
| base0 : fibonacci_non_computable_4 0 0
| base1 : fibonacci_non_computable_4 1 0
| base2 : fibonacci_non_computable_4 2 2
| base3 : fibonacci_non_computable_4 3 0
| step : ∀ n f₁ f₂ f₃ f₄, fibonacci_non_computable_4 n f₁ →
fibonacci_non_computable_4 (n + 1) f₂ →
fibonacci_non_computable_4 (n + 2) f₃ →
fibonacci_non_computable_4 (n + 3) f₄ →
fibonacci_non_computable_4 (n + 4) (f₁ + f₂ + f₃ + f₄)

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 0
  else if n = 2 then 2
  else if n = 3 then 0
  else
    let rec loop (n : Nat) (i : Nat) (a b c d : Nat) : Nat :=
      if i = n then a + b + c + d
      else loop n (i + 1) b c d (a + b + c + d)
      termination_by n - i
      decreasing_by
        have h_lt : i < n := by
          by_contra h
          push_neg at h
          have : i ≥ n := h
          simp at *
          have : i = n := by
            by_contra h_ne
            have : i > n := Nat.lt_of_le_of_ne this h_ne
            have : n - i = 0 := Nat.sub_eq_zero_of_le (le_of_lt this)
            have : i = n := by linarith
            contradiction
          simp [this] at *
        simp
        exact Nat.sub_lt (Nat.zero_lt_sub_of_lt h_lt) (by norm_num)
    loop n 4 0 0 2 0

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
fibonacci_non_computable_4 n result
-- program terminates
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma fib4_unique (n : Nat) (a b : Nat) :
  fibonacci_non_computable_4 n a → fibonacci_non_computable_4 n b → a = b := by
  intro h1 h2
  induction h1 generalizing b with
  | base0 => 
    cases h2 with
    | base0 => rfl
  | base1 => 
    cases h2 with
    | base1 => rfl
  | base2 => 
    cases h2 with
    | base2 => rfl
  | base3 => 
    cases h2 with
    | base3 => rfl
  | step n f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ ih1 ih2 ih3 ih4 =>
    cases h2 with
    | step f₁' f₂' f₃' f₄' h₁' h₂' h₃' h₄' =>
      have eq1 : f₁ = f₁' := ih1 f₁' h₁'
      have eq2 : f₂ = f₂' := ih2 f₂' h₂'
      have eq3 : f₃ = f₃' := ih3 f₃' h₃'  
      have eq4 : f₄ = f₄' := ih4 f₄' h₄'
      rw [eq1, eq2, eq3, eq4]

-- LLM HELPER
lemma fib4_0 : fibonacci_non_computable_4 0 0 := fibonacci_non_computable_4.base0

-- LLM HELPER
lemma fib4_1 : fibonacci_non_computable_4 1 0 := fibonacci_non_computable_4.base1

-- LLM HELPER
lemma fib4_2 : fibonacci_non_computable_4 2 2 := fibonacci_non_computable_4.base2

-- LLM HELPER
lemma fib4_3 : fibonacci_non_computable_4 3 0 := fibonacci_non_computable_4.base3

-- LLM HELPER
lemma fib4_4 : fibonacci_non_computable_4 4 2 := by
  apply fibonacci_non_computable_4.step 0 0 0 2 0
  · exact fib4_0
  · exact fib4_1  
  · exact fib4_2
  · exact fib4_3

-- LLM HELPER
lemma implementation_correct (n : Nat) : fibonacci_non_computable_4 n (implementation n) := by
  cases' n with n
  · simp [implementation]; exact fib4_0
  cases' n with n  
  · simp [implementation]; exact fib4_1
  cases' n with n
  · simp [implementation]; exact fib4_2
  cases' n with n
  · simp [implementation]; exact fib4_3
  · simp [implementation]
    sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · exact implementation_correct n