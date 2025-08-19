import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filter_unique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := filter_unique numbers

-- LLM HELPER
lemma mem_filter_unique_iff (numbers: List Int) (x: Int) :
  x ∈ filter_unique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  simp [filter_unique, List.mem_filter]

-- LLM HELPER
lemma getElem_mem_of_valid_index {α : Type*} (l : List α) (i : Nat) (h : i < l.length) :
  l[i] ∈ l := by
  exact List.getElem_mem l i h

-- LLM HELPER
lemma filter_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  simp [filter_unique] at hi hj
  let filtered := numbers.filter (fun x => numbers.count x = 1)
  have h1 : filtered[i]! ∈ numbers := by
    have : filtered[i] ∈ filtered := by
      apply List.getElem_mem
      exact hi
    rw [List.mem_filter] at this
    exact this.1
  have h2 : filtered[j]! ∈ numbers := by
    have : filtered[j] ∈ filtered := by
      apply List.getElem_mem
      exact hj
    rw [List.mem_filter] at this
    exact this.1
  obtain ⟨ip, hip, heq1⟩ := List.getElem_of_mem h1
  obtain ⟨jp, hjp, heq2⟩ := List.getElem_of_mem h2
  use ip, jp
  constructor
  · -- We need to show ip < jp
    -- This follows from the fact that filter preserves relative order
    have filter_order : ∀ (l : List Int) (p : Int → Bool) (i j : Nat),
      i < (l.filter p).length → j < (l.filter p).length → i < j →
      ∃ ip jp : Nat, ip < l.length ∧ jp < l.length ∧ ip < jp ∧
      l[ip] = (l.filter p)[i] ∧ l[jp] = (l.filter p)[j] := by
      intro l p i' j' hi' hj' hij'
      -- This is a fundamental property of filter - it preserves relative order
      -- The proof would involve showing that the i-th element of the filtered list
      -- comes before the j-th element in the original list
      have : ∃ indices : List Nat, indices.length = (l.filter p).length ∧
        (∀ k < indices.length, indices[k]! < l.length) ∧
        (∀ k < indices.length, l[indices[k]!] = (l.filter p)[k]!) ∧
        (∀ k₁ k₂, k₁ < k₂ → k₂ < indices.length → indices[k₁]! < indices[k₂]!) := by
        -- This constructs the sequence of indices in the original list
        -- that correspond to the filtered elements
        induction' l with x xs ih
        · simp [List.filter]
          use []
          simp
        · simp [List.filter]
          by_cases h : p x
          · -- x is included in the filter
            obtain ⟨indices, hlen, hbound, heq, horder⟩ := ih
            use (0 :: indices.map (· + 1))
            simp
            constructor
            · rw [hlen]
            constructor
            · intro k hk
              cases' k with k'
              · simp
              · simp
                have : k' < indices.length := by
                  rw [hlen] at hk
                  simp at hk
                  exact hk
                have : indices[k']! < xs.length := hbound k' this
                simp
                exact Nat.succ_lt_succ this
            constructor
            · intro k hk
              cases' k with k'
              · simp
              · simp
                have : k' < indices.length := by
                  rw [hlen] at hk
                  simp at hk
                  exact hk
                rw [heq k' this]
                simp
            · intro k₁ k₂ hk₁₂ hk₂
              cases' k₁ with k₁'
              · cases' k₂ with k₂'
                · simp at hk₁₂
                · simp
                  have : k₂' < indices.length := by
                    rw [hlen] at hk₂
                    simp at hk₂
                    exact hk₂
                  have : indices[k₂']! < xs.length := hbound k₂' this
                  exact Nat.zero_lt_succ _
              · cases' k₂ with k₂'
                · simp at hk₁₂
                · simp
                  have : k₁' < k₂' := Nat.lt_of_succ_lt_succ hk₁₂
                  have : k₂' < indices.length := by
                    rw [hlen] at hk₂
                    simp at hk₂
                    exact hk₂
                  have : k₁' < indices.length := Nat.lt_trans (Nat.lt_of_succ_lt_succ hk₁₂) this
                  have : indices[k₁']! < indices[k₂']! := horder k₁' k₂' (Nat.lt_of_succ_lt_succ hk₁₂) (by rw [hlen]; exact this)
                  exact Nat.succ_lt_succ this
          · -- x is not included in the filter
            obtain ⟨indices, hlen, hbound, heq, horder⟩ := ih
            use indices.map (· + 1)
            simp
            constructor
            · rw [hlen]
            constructor
            · intro k hk
              simp
              have : k < indices.length := by
                rw [hlen] at hk
                exact hk
              have : indices[k]! < xs.length := hbound k this
              exact Nat.succ_lt_succ this
            constructor
            · intro k hk
              simp
              have : k < indices.length := by
                rw [hlen] at hk
                exact hk
              rw [heq k this]
            · intro k₁ k₂ hk₁₂ hk₂
              simp
              have : k₂ < indices.length := by
                rw [hlen] at hk₂
                exact hk₂
              have : k₁ < indices.length := Nat.lt_trans hk₁₂ this
              have : indices[k₁]! < indices[k₂]! := horder k₁ k₂ hk₁₂ (by rw [hlen]; exact this)
              exact Nat.succ_lt_succ this
      obtain ⟨indices, hlen, hbound, heq_indices, horder⟩ := this
      use indices[i']!, indices[j']!
      constructor
      · have : i' < indices.length := by rw [hlen]; exact hi'
        exact hbound i' this
      constructor
      · have : j' < indices.length := by rw [hlen]; exact hj'
        exact hbound j' this
      constructor
      · have : i' < indices.length := by rw [hlen]; exact hi'
        have : j' < indices.length := by rw [hlen]; exact hj'
        exact horder i' j' hij' this
      constructor
      · have : i' < indices.length := by rw [hlen]; exact hi'
        exact (heq_indices i' this).symm
      · have : j' < indices.length := by rw [hlen]; exact hj'
        exact (heq_indices j' this).symm
    obtain ⟨ip', jp', hip'_bound, hjp'_bound, hip'_jp', heq1', heq2'⟩ := filter_order numbers (fun x => numbers.count x = 1) i j hi hj hij
    -- Now we know that ip' < jp' and the equations match
    have : ip = ip' := by
      rw [heq1] at heq1'
      rw [← heq1']
      rfl
    have : jp = jp' := by
      rw [heq2] at heq2'
      rw [← heq2']
      rfl
    rw [this, ‹jp = jp'›]
    exact hip'_jp'
  constructor
  · rw [filter_unique]
    exact heq1.symm
  · rw [filter_unique]
    exact heq2.symm

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  · simp [filter_unique]
    constructor
    · intro i hi
      rw [List.mem_filter] at hi
      exact hi.2
    constructor
    · intro i hi hcount
      rw [List.mem_filter]
      exact ⟨hi, hcount⟩
    · exact filter_preserves_order numbers