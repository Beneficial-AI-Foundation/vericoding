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
          · exact Nat.pos_of_ne_zero (ne_of_gt hgt)
        have ih_result := ih (fuel' + 1) (by omega) (n / smallest_prime_factor n) 
          (by omega)
        cases ih_result with
        | inl h_eq =>
          rw [← h_eq]
          rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)]
        | inr h_le =>
          have : n / smallest_prime_factor n ≤ 1 := h_le
          have : n = smallest_prime_factor n := by
            have : n / smallest_prime_factor n = 1 := by
              by_contra h_neq
              have : n / smallest_prime_factor n = 0 := by
                omega
              have : n = 0 := by
                rw [Nat.div_eq_zero_iff_lt] at this
                have : n < smallest_prime_factor n := by
                  simp [this]
                  exact Nat.pos_of_ne_zero (ne_of_gt hgt)
                have : smallest_prime_factor n ≤ n := hle
                omega
              omega
            exact Nat.div_eq_one_iff_eq.mp this
          rw [this]
          rw [Nat.div_self (Nat.pos_of_ne_zero (ne_of_gt hgt))]
          simp

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
        · intro x hx
          have : x ∈ prime_factorization_aux (n / smallest_prime_factor n) fuel' := hx
          have hn : n > 1 := by omega
          have hprime := smallest_prime_factor_is_prime n hn
          have : smallest_prime_factor n ≤ x := by
            induction fuel' using Nat.strong_induction_on generalizing n with
            | h fuel'' ih' =>
              cases fuel'' with
              | zero => simp [prime_factorization_aux] at hx
              | succ fuel''' =>
                simp [prime_factorization_aux] at hx
                split_ifs at hx with h_cond
                · simp at hx
                · simp at hx
                  cases hx with
                  | inl h_eq =>
                    rw [← h_eq]
                    have : n / smallest_prime_factor n > 1 := by omega
                    have : smallest_prime_factor n ≤ smallest_prime_factor (n / smallest_prime_factor n) := by
                      have : smallest_prime_factor (n / smallest_prime_factor n) ∣ (n / smallest_prime_factor n) := by
                        have := smallest_prime_factor_divides (n / smallest_prime_factor n) this
                        exact Nat.dvd_iff_mod_eq_zero.mpr this
                      have : smallest_prime_factor (n / smallest_prime_factor n) * smallest_prime_factor n ≤ n := by
                        have : smallest_prime_factor (n / smallest_prime_factor n) * (n / smallest_prime_factor n) ≤ n := by
                          rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr (smallest_prime_factor_divides n hn))]
                        rw [mul_comm] at this
                        exact Nat.le_div_of_mul_le (Nat.pos_of_ne_zero (ne_of_gt (smallest_prime_factor_gt_one n hn))) this
                      have : smallest_prime_factor (n / smallest_prime_factor n) ≤ n / smallest_prime_factor n := smallest_prime_factor_le (n / smallest_prime_factor n) this
                      have : smallest_prime_factor n ≤ smallest_prime_factor (n / smallest_prime_factor n) := by
                        by_contra h_not
                        have : smallest_prime_factor (n / smallest_prime_factor n) < smallest_prime_factor n := by omega
                        have : smallest_prime_factor (n / smallest_prime_factor n) ∣ n := by
                          have : smallest_prime_factor (n / smallest_prime_factor n) ∣ (n / smallest_prime_factor n) := by
                            exact Nat.dvd_iff_mod_eq_zero.mpr (smallest_prime_factor_divides (n / smallest_prime_factor n) this)
                          have : smallest_prime_factor n ∣ n := Nat.dvd_iff_mod_eq_zero.mpr (smallest_prime_factor_divides n hn)
                          exact Nat.dvd_gcd_mul_gcd_of_coprime this this
                        have : smallest_prime_factor (n / smallest_prime_factor n) ≤ n := Nat.le_of_dvd (by omega) this
                        have : smallest_prime_factor (n / smallest_prime_factor n) ≥ smallest_prime_factor n := by
                          simp [smallest_prime_factor]
                          split_ifs with h_cond
                          · omega
                          · have : (List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) = some (smallest_prime_factor (n / smallest_prime_factor n)) := by
                            simp [List.find?_eq_some]
                            constructor
                            · simp [List.mem_range]
                              omega
                            · constructor
                              · intro y hy hlt
                                simp [smallest_prime_factor] at hlt
                                split_ifs at hlt with h_cond'
                                · omega
                                · cases' h_find : (List.range (n + 1)).find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) with
                                  | none => simp at hlt
                                  | some k => 
                                    have := List.find?_some h_find
                                    simp at this
                                    simp [Option.getD] at hlt
                                    have : y < k := hlt
                                    have : k ≤ n := Nat.le_of_lt_succ (List.mem_range.mp this.1)
                                    by_contra h_cond
                                    simp at h_cond
                                    have : y > 1 ∧ n % y = 0 ∧ Nat.Prime y := h_cond
                                    have : List.find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) (List.range (n + 1)) = some y := by
                                      rw [List.find?_eq_some]
                                      constructor
                                      · simp [List.mem_range]
                                        omega
                                      · constructor
                                        · intro z hz hzlt
                                          by_contra h_z
                                          simp at h_z
                                          have : z > 1 ∧ n % z = 0 ∧ Nat.Prime z := h_z
                                          have : z ≥ k := by
                                            have : List.find? (fun k => decide (1 < k) && (decide (n % k = 0) && decide (Nat.Prime k))) (List.range (n + 1)) = some k := h_find
                                            rw [List.find?_eq_some] at this
                                            exact this.2.1 z hz hzlt
                                          omega
                                        · simp
                                          exact this
                                    rw [this] at h_find
                                    simp at h_find
                                    omega
                              · simp
                                constructor
                                · exact smallest_prime_factor_gt_one (n / smallest_prime_factor n) this
                                · constructor
                                  · exact this
                                  · exact smallest_prime_factor_is_prime (n / smallest_prime_factor n) this
                            omega
                        omega
                      exact this
                  | inr h_mem =>
                    exact ih' fuel''' (by omega) (n / smallest_prime_factor n) h_mem
          exact this
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
            exact Nat.mod_eq_zero_of_dvd (dvd_of_mem x (prime_factorization_aux n n) hx)
          | inr h => 
            exfalso
            omega
        · exact prime_factorization_aux_all_prime n n x hx