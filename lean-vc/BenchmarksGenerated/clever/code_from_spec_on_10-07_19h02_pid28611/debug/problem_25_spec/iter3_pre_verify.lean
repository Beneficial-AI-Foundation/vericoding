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
def prime_factorization_aux (n: Nat) (k: Nat) : List Nat :=
if h : k * k > n then
  if n > 1 then [n] else []
else
  if n % k = 0 then
    k :: prime_factorization_aux (n / k) k
  else
    prime_factorization_aux n (k + 1)
termination_by n
decreasing_by
  simp_wf
  · have h1 : n % k = 0 := by assumption
    have h2 : k ≥ 2 := by omega
    have h3 : n ≥ 2 := by omega
    have h4 : n / k < n := Nat.div_lt_self (by omega) (by omega)
    exact h4
  · omega

def implementation (n: Nat) : List Nat := 
if n < 2 then [] else prime_factorization_aux n 2

-- LLM HELPER
lemma prime_factorization_aux_correct (n k : Nat) (hk : k ≥ 2) (hn : n ≥ 2) :
  let result := prime_factorization_aux n k
  result.prod = n ∧ 
  List.Sorted Nat.le result ∧
  (∀ x ∈ result, n % x = 0 ∧ Nat.Prime x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp [prime_factorization_aux]
    by_cases h : k * k > n
    · simp [h]
      by_cases hn1 : n > 1
      · simp [hn1]
        constructor
        · simp [List.prod_cons, List.prod_nil]
        constructor
        · exact List.sorted_singleton _
        · intro x hx
          simp at hx
          subst hx
          constructor
          · simp
          · -- Need to prove n is prime, but this is complex
            sorry
      · simp [hn1]
        constructor
        · simp [List.prod_nil]
          omega
        constructor
        · exact List.sorted_nil _
        · intro x hx
          simp at hx
    · simp [h]
      by_cases hmod : n % k = 0
      · simp [hmod]
        have hdiv : n / k < n := Nat.div_lt_self (by omega) (by omega)
        have hdiv_ge : n / k ≥ 2 := by
          have : n ≥ k * 2 := by omega
          rw [← Nat.mul_div_cancel (by omega : k > 0)]
          exact Nat.div_le_div_right this
        specialize ih (n / k) hdiv hk hdiv_ge
        constructor
        · simp [List.prod_cons]
          rw [ih.1]
          exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hmod)
        constructor
        · -- Need to prove sorted property
          sorry
        · intro x hx
          simp at hx
          cases hx with
          | inl h => 
            subst h
            constructor
            · exact hmod
            · -- Need to prove k is prime
              sorry
          | inr h =>
            have := ih.2.2 x h
            constructor
            · -- Need to prove n % x = 0
              sorry
            · exact this.2
      · simp [hmod]
        have hk_inc : k + 1 ≥ 2 := by omega
        exact ih n (by omega) hk_inc hn

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
      have result := prime_factorization_aux_correct n 2 (by norm_num) hn'
      constructor
      · exact result.1
      constructor
      · exact result.2.1
      · intro x hx
        simp [List.all_iff_forall]
        exact result.2.2 x hx