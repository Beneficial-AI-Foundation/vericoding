def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def findMinPrime (lst: List Nat) : Option Nat :=
  let primes := lst.filter Nat.Prime
  if primes.isEmpty then none
  else some (primes.minimum?)

-- LLM HELPER
def digitSum (n: Nat) : Nat :=
  (Nat.digits 10 n).sum

def implementation (lst: List Nat) : Nat :=
  match findMinPrime lst with
  | none => 0
  | some minPrime => digitSum minPrime

-- LLM HELPER
lemma digitSum_pos_of_prime (p: Nat) (hp: Nat.Prime p) : digitSum p > 0 := by
  sorry

-- LLM HELPER
lemma findMinPrime_correct (lst: List Nat) :
  match findMinPrime lst with
  | none => ¬lst.any (fun num => Nat.Prime num)
  | some p => Nat.Prime p ∧ p ∈ lst ∧ (∀ q ∈ lst, Nat.Prime q → p ≤ q) := by
  sorry

-- LLM HELPER
lemma list_any_iff_filter_nonempty (lst: List Nat) :
  lst.any (fun num => Nat.Prime num) ↔ (lst.filter Nat.Prime).length > 0 := by
  sorry

-- LLM HELPER
lemma mem_implies_get_at_some_index (lst: List Nat) (x: Nat) (hx: x ∈ lst) :
  ∃ i, i < lst.length ∧ lst.get! i = x := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use implementation lst
  constructor
  · rfl
  · intro h_any_prime
    unfold implementation
    have h_find := findMinPrime_correct lst
    cases h_find_eq : findMinPrime lst with
    | none => 
      have h_no_prime := h_find
      rw [h_find_eq] at h_no_prime
      exact absurd h_any_prime h_no_prime
    | some minPrime =>
      have h_min_prime := h_find
      rw [h_find_eq] at h_min_prime
      obtain ⟨h_prime, h_mem, h_min⟩ := h_min_prime
      constructor
      · exact digitSum_pos_of_prime minPrime h_prime
      · obtain ⟨i, hi_bound, hi_eq⟩ := mem_implies_get_at_some_index lst minPrime h_mem
        use i
        constructor
        · exact hi_bound
        · constructor
          · rw [hi_eq]; exact h_prime
          · constructor
            · intro j hj_bound hj_prime
              rw [hi_eq]
              exact h_min (lst.get! j) (by sorry) hj_prime
            · rw [hi_eq]; rfl