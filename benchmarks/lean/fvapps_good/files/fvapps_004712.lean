-- <vc-preamble>
def fib : Nat → Nat 
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fibs_fizz_buzz (n : Nat) : List (String ⊕ Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fibs_fizz_buzz_length (n : Nat) :
  List.length (fibs_fizz_buzz n) = n :=
sorry

theorem fibs_fizz_buzz_first_values {n : Nat} (h : n ≥ 1) :
  match fibs_fizz_buzz n with
  | [] => False
  | x::_ => x = Sum.inr 1
:=
sorry

theorem fibs_fizz_buzz_first_two {n : Nat} (h : n ≥ 2) :
  match fibs_fizz_buzz n with
  | []      => False 
  | [_]     => False
  | x::y::_ => x = Sum.inr 1 ∧ y = Sum.inr 1
:=
sorry

theorem fibs_fizz_buzz_rules {n : Nat} (i : Nat) (h : i < n) :
  let result := (fibs_fizz_buzz n).get ⟨i, by {
    rw [fibs_fizz_buzz_length n]
    exact h
  }⟩
  let fibonacci := fib i
  match result with
  | Sum.inl s => 
    (fibonacci % 15 = 0 ∧ s = "FizzBuzz") ∨
    (fibonacci % 3 = 0 ∧ fibonacci % 5 ≠ 0 ∧ s = "Fizz") ∨
    (fibonacci % 5 = 0 ∧ fibonacci % 3 ≠ 0 ∧ s = "Buzz")
  | Sum.inr k => fibonacci % 3 ≠ 0 ∧ fibonacci % 5 ≠ 0 ∧ k = fibonacci
:=
sorry
-- </vc-theorems>