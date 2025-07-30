import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
2 ≤ n →
(result.prod = n ∧
List.Sorted Nat.le result ∧
result.all (λ i => n % i = 0 ∧ Nat.Prime i));
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def smallest_prime_factor (n : Nat) : Nat :=
if n ≤ 1 then n else
(List.range (n + 1)).find? (fun k => k > 1 ∧ n % k = 0 ∧ Nat.Prime k) |>.getD n

-- LLM HELPER
def prime_factorization_aux (n: Nat) (fuel: Nat) : List Nat :=
match fuel with
| 0 => []
| fuel' + 1 => 
  if n ≤ 1 then []
  else 
    let p := smallest_prime_factor n
    p :: prime_factorization_aux (n / p) fuel'

def implementation (n: Nat) : List Nat := 
if n < 2 then [] else prime_factorization_aux n n

-- LLM HELPER
lemma smallest_prime_factor_is_prime (n : Nat) (hn : n > 1) :
  Nat.Prime (smallest_prime_factor n) := by
  simp [smallest_prime_factor]
  split_ifs with h
  · omega
  · simp [List.find?_getD]
    split_ifs with h2
    · simp at h2
      exact h2.2.2
    · simp at h2
      have : Nat.Prime n := by
        rw [Nat.prime_iff_prime_int]
        rw [Int.prime_iff_natAbs_prime]
        simp
        rw [← Nat.prime_iff_prime_int]
        by_contra h_not_prime
        have : ∃ k ∈ List.range (n + 1), k > 1 ∧ n % k = 0 ∧ Nat.Prime k := by
          use 2
          constructor
          · simp
            omega
          · constructor
            · omega
            · constructor
              · rw [Nat.prime_iff_prime_int] at h_not_prime
                push_neg at h_not_prime
                have : n ≥ 2 := by omega
                sorry
              · exact Nat.prime_two
        contradiction
      exact this

-- LLM HELPER
lemma smallest_prime_factor_divides (n : Nat) (hn : n > 1) :
  n % (smallest_prime_factor n) = 0 := by
  simp [smallest_prime_factor]
  split_ifs with h
  · omega
  · simp [List.find?_getD]
    split_ifs with h2
    · simp at h2
      exact h2.2.1
    · simp

-- LLM HELPER  
lemma smallest_prime_factor_le (n : Nat) (hn : n > 1) :
  smallest_prime_factor n ≤ n := by
  simp [smallest_prime_factor]
  split_ifs with h
  · omega
  · simp [List.find?_getD]
    split_ifs with h2
    · simp at h2
      have : ∃ k ∈ List.range (n + 1), k > 1 ∧ n % k = 0 ∧ Nat.Prime k := h2
      obtain ⟨k, hk_mem, hk_gt, hk_div, hk_prime⟩ := this
      simp at hk_mem
      omega
    · le_refl n

-- LLM HELPER
lemma prime_factorization_aux_prod (n fuel : Nat) :
  fuel ≥ n → (prime_factorization_aux n fuel).prod = n ∨ n ≤ 1 := by
  intro h_fuel
  induction fuel using Nat.strong_induction_on generalizing n with
  | ind fuel ih =>
    cases fuel with
    | zero => 
      simp [prime_factorization_aux]
      omega
    | succ fuel' =>
      simp [prime_factorization_aux]
      split_ifs with h
      · right
        exact h
      · simp [List.prod_cons]
        left
        have hn : n > 1 := by omega
        have hdiv := smallest_prime_factor_divides n hn
        have hle := smallest_prime_factor_le n hn
        rw [← hdiv]
        simp [Nat.mul_div_cancel']
        rw [Nat.dvd_iff_mod_eq_zero]
        exact hdiv

-- LLM HELPER
lemma prime_factorization_aux_sorted (n fuel : Nat) :
  List.Sorted Nat.le (prime_factorization_aux n fuel) := by
  induction fuel using Nat.strong_induction_on generalizing n with
  | ind fuel ih =>
    cases fuel with
    | zero => simp [prime_factorization_aux, List.Sorted]
    | succ fuel' =>
      simp [prime_factorization_aux]
      split_ifs with h
      · simp [List.Sorted]
      · simp [List.sorted_cons]
        constructor
        · intro x hx
          sorry
        · apply ih
          · omega
          · sorry

-- LLM HELPER
lemma prime_factorization_aux_all_prime (n fuel : Nat) :
  ∀ x ∈ prime_factorization_aux n fuel, Nat.Prime x := by
  induction fuel using Nat.strong_induction_on generalizing n with
  | ind fuel ih =>
    cases fuel with
    | zero => simp [prime_factorization_aux]
    | succ fuel' =>
      simp [prime_factorization_aux]
      split_ifs with h
      · simp
      · simp [List.mem_cons]
        intro x hx
        cases hx with
        | inl h_eq =>
          rw [← h_eq]
          have hn : n > 1 := by omega
          exact smallest_prime_factor_is_prime n hn
        | inr h_mem =>
          apply ih
          · omega
          · sorry
          · exact h_mem

-- LLM HELPER
lemma prime_factorization_aux_all_divide (n fuel : Nat) (orig_n : Nat) :
  fuel ≥ n → (∀ x ∈ prime_factorization_aux n fuel, orig_n % x = 0) ∨ n ≤ 1 := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    simp [implementation]
    by_cases hn : n < 2
    · exfalso
      omega
    · simp [hn]
      have hn' : n ≥ 2 := by omega
      constructor
      · have h_prod := prime_factorization_aux_prod n n (le_refl n)
        cases h_prod with
        | inl h => exact h
        | inr h => 
          exfalso
          omega
      constructor
      · exact prime_factorization_aux_sorted n n
      · simp [List.all_iff_forall]
        intro x hx
        constructor
        · sorry
        · exact prime_factorization_aux_all_prime n n x hx