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
lemma filter_unique_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  simp [filter_unique] at hi hj
  have h1 : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
    have : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers.filter (fun x => numbers.count x = 1) := by
      apply List.getElem_mem
      exact hi
    rw [List.mem_filter] at this
    exact this.1
  have h2 : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
    have : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers.filter (fun x => numbers.count x = 1) := by
      apply List.getElem_mem
      exact hj
    rw [List.mem_filter] at this
    exact this.1
  obtain ⟨ip, hip, heq1⟩ := List.getElem_of_mem h1
  obtain ⟨jp, hjp, heq2⟩ := List.getElem_of_mem h2
  have order_preserved : ip < jp := by
    by_contra h
    push_neg at h
    have : jp ≤ ip := Nat.le_of_not_gt h
    have jp_lt_ip_or_eq : jp < ip ∨ jp = ip := Nat.lt_or_eq_of_le this
    cases jp_lt_ip_or_eq with
    | inl hjp_lt_hip =>
      have : j < i := by
        apply List.filter_preserves_relative_order
        · exact hjp
        · exact hip
        · exact hjp_lt_hip
        · simp
      linarith
    | inr hjp_eq_hip =>
      rw [hjp_eq_hip] at heq2
      rw [heq1] at heq2
      have : (numbers.filter (fun x => numbers.count x = 1))[i]! = (numbers.filter (fun x => numbers.count x = 1))[j]! := by
        rw [heq2]
      have : i = j := by
        apply List.getElem_inj_of_nodup
        · apply List.filter_nodup_of_count_one
        · exact hi
        · exact hj
        · exact this
      linarith
  exact ⟨ip, jp, order_preserved, heq1, heq2⟩

-- LLM HELPER
lemma List.filter_nodup_of_count_one {α : Type*} [DecidableEq α] (l : List α) :
  (l.filter (fun x => l.count x = 1)).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_of_count_le_one
  intro a
  by_cases h : a ∈ l
  · simp [List.count_pos.mpr h]
  · simp [List.count_eq_zero.mpr h]

-- LLM HELPER
lemma List.filter_preserves_relative_order {α : Type*} (l : List α) (p : α → Bool) 
  (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) (hp : p l[i]! ∧ p l[j]!) :
  ∃ i' j' : Nat, i' < j' ∧ i' < (l.filter p).length ∧ j' < (l.filter p).length ∧ 
  (l.filter p)[i']! = l[i]! ∧ (l.filter p)[j']! = l[j]! := by
  sorry

-- LLM HELPER
lemma List.getElem_of_mem {α : Type*} (l : List α) (a : α) (h : a ∈ l) :
  ∃ i : Nat, i < l.length ∧ l[i]! = a := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h => 
      use 0
      simp [h]
    | inr h =>
      obtain ⟨i, hi, heq⟩ := ih h
      use i + 1
      simp [hi, heq]

-- LLM HELPER
lemma List.getElem_inj_of_nodup {α : Type*} (l : List α) (h : l.Nodup) 
  (i j : Nat) (hi : i < l.length) (hj : j < l.length) (heq : l[i]! = l[j]!) : i = j := by
  by_contra hne
  wlog h_ord : i < j
  · exact this h j i hj hi heq.symm (Ne.symm hne) (Nat.lt_of_le_of_ne (Nat.le_of_not_gt h_ord) hne)
  have : l[i]! ∈ l.take j := by
    rw [List.mem_take]
    exact ⟨heq ▸ l[j]!, ⟨by simp [List.getElem_mem], h_ord⟩⟩
  have : l[j]! ∈ l.drop (j + 1) := by
    rw [List.mem_drop]
    use j
    simp [hj]
  have : l[i]! ∈ l.take j ∩ l.drop (j + 1) := by
    rw [heq]
    sorry
  have : (l.take j ∩ l.drop (j + 1)).length = 0 := by
    apply List.eq_nil_of_length_eq_zero
    sorry
  simp at this

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  constructor
  · intro i hi
    rw [mem_filter_unique_iff] at hi
    exact hi.2
  constructor
  · intro i hi hcount
    rw [mem_filter_unique_iff]
    exact ⟨hi, hcount⟩
  · exact filter_unique_preserves_order numbers