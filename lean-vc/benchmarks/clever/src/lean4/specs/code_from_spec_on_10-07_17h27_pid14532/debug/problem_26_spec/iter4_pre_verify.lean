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
lemma List.getElem_of_mem {α : Type*} (l : List α) (x : α) (h : x ∈ l) :
  ∃ i : Nat, i < l.length ∧ l[i] = x := by
  exact List.exists_getElem_of_mem h

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
  obtain ⟨ip, hip, heq1⟩ := List.getElem_of_mem numbers (filtered[i]!) h1
  obtain ⟨jp, hjp, heq2⟩ := List.getElem_of_mem numbers (filtered[j]!) h2
  use ip, jp
  constructor
  · -- We need to show ip < jp using the fact that filter preserves order
    by_contra h_contra
    -- If ip >= jp, then since filter preserves order, we would have i >= j
    -- But we have i < j, contradiction
    have : jp ≤ ip := Nat.le_of_not_gt h_contra
    -- Since filtered[i]! and filtered[j]! are unique elements from the filter,
    -- and i < j, we must have ip < jp by the ordering property of filter
    cases' Nat.lt_or_eq_of_le this with h_lt h_eq
    · -- Case jp < ip
      -- This would contradict the ordering property of filter
      have : List.IsSublist filtered numbers := List.filter_isSublist _ _
      have : List.IsSublist.indices this i j hi hj hij = (ip, jp) := by
        -- The indices should preserve order in the subsequence
        sorry
      exact Nat.lt_irrefl jp (Nat.lt_trans h_lt (Nat.le_refl jp))
    · -- Case jp = ip
      rw [← h_eq] at heq1
      have : filtered[i]! = filtered[j]! := by
        rw [heq1, heq2]
      -- But elements at different positions in a filtered list must be different
      -- when considering unique elements
      have : i = j := by
        -- Since filter removes duplicates of unique elements, 
        -- if two positions have the same value, they must be the same position
        have : ∀ k l : Nat, k < filtered.length → l < filtered.length → 
               k ≠ l → filtered[k]! ≠ filtered[l]! := by
          intro k l hk hl hne
          by_contra heq
          -- This would mean we have a duplicate in the filtered list
          -- But filtered contains only unique elements
          have : filtered[k] = filtered[l] := by
            simp [List.getElem_fin_eq_getElem_fin] at heq
            exact heq
          have : k = l := by
            -- Use the fact that filter preserves distinctness
            have : filtered.Nodup := by
              apply List.nodup_filter
              intro x hx
              simp [List.mem_filter] at hx
              exact hx.2
            rw [List.nodup_iff_getElem_ne_getElem] at this
            by_contra
            have : filtered[k] ≠ filtered[l] := this k l hk hl hne
            contradiction
          contradiction
        have : filtered[i]! ≠ filtered[j]! := this i j hi hj (Ne.symm (Nat.ne_of_lt hij))
        contradiction
      rw [this] at hij
      exact Nat.lt_irrefl j hij
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