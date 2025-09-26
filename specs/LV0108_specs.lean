-- <vc-preamble>
@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))

theorem isPrime_spec_satisfied (n: Nat) (h_precond : isPrime_precond (n)) :
    isPrime_postcond (n) (isPrime (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>