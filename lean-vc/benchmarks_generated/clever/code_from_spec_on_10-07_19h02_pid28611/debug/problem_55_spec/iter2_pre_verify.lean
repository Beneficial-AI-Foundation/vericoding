import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
def fib_helper : Nat → Nat × Nat
| 0 => (0, 1)
| n + 1 => 
  let (a, b) := fib_helper n
  (b, a + b)

def implementation (n: Nat) : Nat := (fib_helper n).1

-- LLM HELPER
lemma fib_helper_correct (n: Nat) : 
  fibonacci_non_computable n (fib_helper n).1 ∧ 
  fibonacci_non_computable (n + 1) (fib_helper n).2 := by
  induction n with
  | zero => 
    simp [fib_helper, fibonacci_non_computable]
  | succ n ih =>
    simp [fib_helper]
    let (a, b) := fib_helper n
    simp at ih ⊢
    cases n with
    | zero =>
      simp [fib_helper, fibonacci_non_computable]
      constructor
      · exact rfl
      · use 0, 1
        simp [fibonacci_non_computable]
    | succ m =>
      simp [fibonacci_non_computable]
      constructor
      · exact ih.2
      · use (fib_helper m).1, (fib_helper m).2
        constructor
        · exact (fib_helper_correct m).1
        constructor
        · exact (fib_helper_correct m).2
        · rfl

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  exact (fib_helper_correct n).1