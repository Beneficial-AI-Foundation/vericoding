-- <vc-preamble>
import Mathlib.Data.Nat.Prime.Defs

@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  primes.all (fun p => Nat.Prime p)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))

theorem findExponents_spec_satisfied (n: Nat) (primes: List Nat) (h_precond : findExponents_precond (n) (primes)) :
    findExponents_postcond (n) (primes) (findExponents (n) (primes) h_precond) h_precond := by
  sorry
-- </vc-theorems>