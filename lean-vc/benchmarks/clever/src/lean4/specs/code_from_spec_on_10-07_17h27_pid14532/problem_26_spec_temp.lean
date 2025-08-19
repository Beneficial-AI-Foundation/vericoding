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
lemma getElem_of_mem {α : Type*} (l : List α) (x : α) (h : x ∈ l) :
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
    have mem_filtered : filtered[i] ∈ filtered := by
      apply List.getElem_mem
      exact hi
    rw [List.mem_filter] at mem_filtered
    exact mem_filtered.1
  have h2 : filtered[j]! ∈ numbers := by
    have mem_filtered : filtered[j] ∈ filtered := by
      apply List.getElem_mem
      exact hj
    rw [List.mem_filter] at mem_filtered
    exact mem_filtered.1
  obtain ⟨ip, hip, heq1⟩ := getElem_of_mem numbers (filtered[i]!) h1
  obtain ⟨jp, hjp, heq2⟩ := getElem_of_mem numbers (filtered[j]!) h2
  use ip, jp
  constructor
  · -- We need to show ip < jp using the fact that filter preserves order
    have : List.IsSublist filtered numbers := List.filter_isSublist _ _
    have order_preserved : ∀ (a b : Nat), a < filtered.length → b < filtered.length → a < b →
      ∃ (ia ib : Nat), ia < ib ∧ filtered[a] = numbers[ia] ∧ filtered[b] = numbers[ib] := by
      intro a b ha hb hab
      have : ∃ indices : List Nat, indices.length = filtered.length ∧ 
             (∀ k < filtered.length, k < indices.length ∧ indices[k]! < numbers.length ∧ 
              filtered[k] = numbers[indices[k]!]) ∧
             (∀ k l, k < indices.length → l < indices.length → k < l → indices[k]! < indices[l]!) := by
        apply List.isSublist_indices_exist
        exact this
      obtain ⟨indices, hlen, hvalid, horder⟩ := this
      use indices[a]!, indices[b]!
      constructor
      · apply horder
        · rw [← hlen]; exact ha
        · rw [← hlen]; exact hb
        · exact hab
      constructor
      · exact (hvalid a ha).2.2
      · exact (hvalid b hb).2.2
    obtain ⟨ia, ib, horder, heqa, heqb⟩ := order_preserved i j hi hj hij
    have : filtered[i]! = numbers[ia] := by
      rw [← heqa]
      simp [List.getElem_fin_eq_getElem_fin]
    have : filtered[j]! = numbers[ib] := by
      rw [← heqb]
      simp [List.getElem_fin_eq_getElem_fin]
    have : ia = ip := by
      apply List.getElem_inj
      · exact hip
      · rw [← heq1, this]
    have : ib = jp := by
      apply List.getElem_inj
      · exact hjp
      · rw [← heq2, this]
    rw [← this, ← this]
    exact horder
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
  · constructor
    · intro i hi
      rw [mem_filter_unique_iff] at hi
      exact hi.2
    constructor
    · intro i hi hcount
      rw [mem_filter_unique_iff]
      exact ⟨hi, hcount⟩
    · exact filter_preserves_order numbers