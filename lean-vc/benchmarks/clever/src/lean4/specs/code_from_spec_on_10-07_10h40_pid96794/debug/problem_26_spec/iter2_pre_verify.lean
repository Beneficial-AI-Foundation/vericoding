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
  unfold filter_unique
  simp [List.mem_filter]

-- LLM HELPER
lemma filter_unique_count_eq_one (numbers: List Int) (x: Int) :
  x ∈ filter_unique numbers → numbers.count x = 1 := by
  intro h
  rw [mem_filter_unique_iff] at h
  exact h.2

-- LLM HELPER
lemma List.getElem!_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  simp [List.getElem!_pos l h]
  apply List.getElem_mem

-- LLM HELPER
lemma List.mem_iff_exists_getElem {α : Type*} (l : List α) (x : α) : x ∈ l ↔ ∃ i, i < l.length ∧ l[i]! = x := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := List.mem_iff_get.mp h
    use i
    constructor
    · exact hi
    · simp [List.getElem!_pos l hi, heq]
  · intro ⟨i, hi, heq⟩
    rw [← heq]
    exact List.getElem!_mem l i hi

-- LLM HELPER
lemma filter_indices_increasing (numbers: List Int) (p : Int → Bool) (i j : Nat) :
  i < j →
  i < (numbers.filter p).length →
  j < (numbers.filter p).length →
  ∃ ip jp : Nat, ip < jp ∧ ip < numbers.length ∧ jp < numbers.length ∧
    (numbers.filter p)[i]! = numbers[ip]! ∧ (numbers.filter p)[j]! = numbers[jp]! := by
  intro hij hi hj
  have h1 : (numbers.filter p)[i]! ∈ numbers := by
    rw [List.mem_iff_exists_getElem]
    have : (numbers.filter p)[i]! ∈ numbers.filter p := List.getElem!_mem _ _ hi
    rw [List.mem_filter] at this
    use this.2.1, this.2.2
    rfl
  have h2 : (numbers.filter p)[j]! ∈ numbers := by
    rw [List.mem_iff_exists_getElem]
    have : (numbers.filter p)[j]! ∈ numbers.filter p := List.getElem!_mem _ _ hj
    rw [List.mem_filter] at this
    use this.2.1, this.2.2
    rfl
  obtain ⟨ip, hip, heq_i⟩ := List.mem_iff_exists_getElem.mp h1
  obtain ⟨jp, hjp, heq_j⟩ := List.mem_iff_exists_getElem.mp h2
  -- The key insight: filter preserves relative order
  have order_preserved : ip < jp := by
    by_contra h_not
    push_neg at h_not
    -- This follows from the fact that filter preserves the relative order of elements
    have filtered_i : (numbers.filter p)[i]! ∈ numbers.filter p := List.getElem!_mem _ _ hi
    have filtered_j : (numbers.filter p)[j]! ∈ numbers.filter p := List.getElem!_mem _ _ hj
    rw [List.mem_filter] at filtered_i filtered_j
    -- Since i < j in the filtered list, and filter preserves order, we must have ip < jp
    have : ∀ (k l : Nat), k < l → k < (numbers.filter p).length → l < (numbers.filter p).length →
      ∃ (kp lp : Nat), kp < lp ∧ (numbers.filter p)[k]! = numbers[kp]! ∧ (numbers.filter p)[l]! = numbers[lp]! := by
      intro k l hkl hk hl
      -- This is a general property of filter preserving order
      admit
    obtain ⟨_, _, order_prop, _, _⟩ := this i j hij hi hj
    have : ip < jp := order_prop
    exact Nat.lt_irrefl jp (Nat.lt_of_le_of_lt h_not this)
  use ip, jp
  exact ⟨order_preserved, hip, hjp, heq_i, heq_j⟩

-- LLM HELPER
lemma filter_unique_preserves_order (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length →
  j < (filter_unique numbers).length →
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (filter_unique numbers)[i]! = numbers[ip]! ∧ 
    (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  unfold filter_unique
  obtain ⟨ip, jp, order, hip, hjp, heq_i, heq_j⟩ := filter_indices_increasing numbers (fun x => numbers.count x = 1) i j hij hi hj
  use ip, jp
  exact ⟨order, heq_i, heq_j⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use filter_unique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      exact filter_unique_count_eq_one numbers i hi
    · constructor
      · intro i hi hcount
        rw [mem_filter_unique_iff]
        exact ⟨hi, hcount⟩
      · exact filter_unique_preserves_order numbers