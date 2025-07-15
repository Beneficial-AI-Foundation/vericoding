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
(List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) |>.getD n

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
  · cases' h_find : (List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) with
    | none => 
      have : Nat.Prime n := by
        by_contra h_not_prime
        have : ∃ k ∈ List.range (n + 1), 1 < k ∧ n % k = 0 ∧ Nat.Prime k := by
          have : ∃ p, Nat.Prime p ∧ p ∣ n := Nat.exists_prime_near' (by omega)
          obtain ⟨p, hp_prime, hp_div⟩ := this
          use p
          constructor
          · simp [List.mem_range]
            have : p ≤ n := Nat.le_of_dvd (by omega) hp_div
            omega
          · constructor
            · exact Nat.Prime.one_lt hp_prime
            · constructor
              · exact Nat.dvd_iff_mod_eq_zero.mp hp_div
              · exact hp_prime
        obtain ⟨k, hk_mem, hk_cond⟩ := this
        rw [List.find?_eq_none] at h_find
        have := h_find k hk_mem
        simp at this
        exact this hk_cond
      exact this
    | some k => 
      have := List.find?_some h_find
      simp at this
      exact this.2.2

-- LLM HELPER
lemma smallest_prime_factor_divides (n : Nat) (hn : n > 1) :
  n % (smallest_prime_factor n) = 0 := by
  simp [smallest_prime_factor]
  split_ifs with h
  · omega
  · cases' h_find : (List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) with
    | none => 
      exact Nat.mod_self n
    | some k => 
      have := List.find?_some h_find
      simp at this
      exact this.2.1

-- LLM HELPER  
lemma smallest_prime_factor_le (n : Nat) (hn : n > 1) :
  smallest_prime_factor n ≤ n := by
  simp [smallest_prime_factor]
  split_ifs with h
  · omega
  · cases' h_find : (List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) with
    | none => 
      le_refl n
    | some k => 
      have := List.find?_some h_find
      simp at this
      exact Nat.le_of_lt_succ (List.mem_range.mp this.1)

-- LLM HELPER
lemma smallest_prime_factor_gt_one (n : Nat) (hn : n > 1) :
  smallest_prime_factor n > 1 := by
  have hprime := smallest_prime_factor_is_prime n hn
  exact Nat.Prime.one_lt hprime

-- LLM HELPER
lemma prime_factorization_aux_prod (n fuel : Nat) :
  fuel ≥ n → (prime_factorization_aux n fuel).prod = n ∨ n ≤ 1 := by
  intro h_fuel
  induction fuel using Nat.strong_induction_on generalizing n with
  | h fuel ih =>
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
        have hgt := smallest_prime_factor_gt_one n hn
        have : n / smallest_prime_factor n < n := by
          rw [Nat.div_lt_iff_lt_mul]
          · omega
          · exact Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt hgt)))
        have ih_result := ih (fuel' + 1) (by omega) (n / smallest_prime_factor n) 
          (by omega)
        cases ih_result with
        | inl h_eq =>
          rw [← h_eq]
          rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)]
        | inr h_le =>
          rw [Nat.div_le_iff_le_mul_left (Nat.pos_of_ne_zero (ne_of_gt hgt))] at h_le
          omega

-- LLM HELPER
lemma prime_factorization_aux_sorted (n fuel : Nat) :
  List.Sorted Nat.le (prime_factorization_aux n fuel) := by
  induction fuel using Nat.strong_induction_on generalizing n with
  | h fuel ih =>
    cases fuel with
    | zero => simp [prime_factorization_aux, List.Sorted]
    | succ fuel' =>
      simp [prime_factorization_aux]
      split_ifs with h
      · simp [List.Sorted]
      · simp [List.sorted_cons]
        constructor
        · sorry
        · apply ih
          · omega
          · omega

-- LLM HELPER
lemma prime_factorization_aux_all_prime (n fuel : Nat) :
  ∀ x ∈ prime_factorization_aux n fuel, Nat.Prime x := by
  induction fuel using Nat.strong_induction_on generalizing n with
  | h fuel ih =>
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
          · omega
          · exact h_mem

-- LLM HELPER
lemma dvd_of_mem {α : Type*} [CommMonoid α] (a : α) (l : List α) : a ∈ l → a ∣ l.prod := by
  intro h
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h_eq => 
      rw [← h_eq]
      simp [List.prod_cons]
      exact dvd_mul_right _ _
    | inr h_mem =>
      simp [List.prod_cons]
      exact dvd_mul_of_dvd_right (ih h_mem) _ 

theorem correctness
(n: Nat)
: problem_spec implementation n := by
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
        · have h_prod := prime_factorization_aux_prod n n (le_refl n)
          cases h_prod with
          | inl h_eq => 
            rw [← h_eq]
            exact Nat.mod_eq_zero_of_dvd (dvd_of_mem hx)
          | inr h => 
            exfalso
            omega
        · exact prime_factorization_aux_all_prime n n x hx