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
lemma filter_preserves_order (l : List Int) (p : Int → Bool) :
  ∀ i j : Nat, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ ip < l.length ∧ jp < l.length ∧ 
  (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intros i j hi hj hij
  have h1 : ∃ ip, ip < l.length ∧ (l.filter p)[i]! = l[ip]! := by
    have mem_orig : (l.filter p)[i]! ∈ l := by
      have mem_filtered : (l.filter p)[i]! ∈ l.filter p := List.getElem_mem _ _ hi
      exact List.mem_of_mem_filter mem_filtered
    exact List.mem_iff_getElem.mp mem_orig
  have h2 : ∃ jp, jp < l.length ∧ (l.filter p)[j]! = l[jp]! := by
    have mem_orig : (l.filter p)[j]! ∈ l := by
      have mem_filtered : (l.filter p)[j]! ∈ l.filter p := List.getElem_mem _ _ hj
      exact List.mem_of_mem_filter mem_filtered
    exact List.mem_iff_getElem.mp mem_orig
  obtain ⟨ip, hip_len, heq1⟩ := h1
  obtain ⟨jp, hjp_len, heq2⟩ := h2
  
  have order_preserved : ip < jp := by
    by_contra h
    push_neg at h
    have : jp ≤ ip := Nat.le_of_not_gt h
    cases' Nat.lt_or_eq_of_le this with hjp_lt_hip hjp_eq_hip
    · have filtered_order : j < i := by
        apply List.filter_index_lt_of_index_lt
        exact hjp_lt_hip
        rw [←heq1, ←heq2]
        simp
      linarith
    · rw [hjp_eq_hip] at heq2
      rw [heq1] at heq2
      have unique_filter : (l.filter p)[i]! = (l.filter p)[j]! := heq2
      have same_index : i = j := by
        have : List.Nodup (l.filter p) ∨ ¬List.Nodup (l.filter p) := Classical.em _
        cases this with
        | inl nodup =>
          exact List.getElem_inj_of_nodup nodup hi hj unique_filter
        | inr not_nodup =>
          by_contra h_neq
          have : i ≠ j := h_neq
          have : (l.filter p)[i]! ≠ (l.filter p)[j]! := by
            apply List.getElem_ne_of_ne_index
            exact this
          contradiction
      linarith
  exact ⟨ip, jp, order_preserved, hip_len, hjp_len, heq1, heq2⟩

-- LLM HELPER
lemma filter_unique_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intros i j hi hj hij
  have h := filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
  obtain ⟨ip, jp, h_order, _, _, heq1, heq2⟩ := h
  exact ⟨ip, jp, h_order, heq1, heq2⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use filter_unique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      rw [mem_filter_unique_iff] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        rw [mem_filter_unique_iff]
        exact ⟨hi, hcount⟩
      · exact filter_unique_preserves_order numbers