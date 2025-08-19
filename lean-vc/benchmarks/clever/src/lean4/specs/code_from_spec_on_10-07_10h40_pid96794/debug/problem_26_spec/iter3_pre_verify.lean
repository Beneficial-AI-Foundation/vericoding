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
  have : l[i]! = l[i] := List.getElem!_pos l h
  rw [this]
  exact List.getElem_mem l i h

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
lemma filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) (i j : Nat) :
  i < j →
  i < (l.filter p).length →
  j < (l.filter p).length →
  ∃ ip jp : Nat, ip < jp ∧ ip < l.length ∧ jp < l.length ∧
    (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro hij hi hj
  -- Get the elements at positions i and j in the filtered list
  have elem_i := List.getElem!_mem (l.filter p) i hi
  have elem_j := List.getElem!_mem (l.filter p) j hj
  
  -- These elements must be in the original list
  rw [List.mem_filter] at elem_i elem_j
  
  -- Find their positions in the original list
  obtain ⟨ip, hip, heq_i⟩ := List.mem_iff_exists_getElem.mp elem_i.1
  obtain ⟨jp, hjp, heq_j⟩ := List.mem_iff_exists_getElem.mp elem_j.1
  
  -- The key property: filter preserves relative order
  have order_preserved : ip < jp := by
    -- This follows from the definition of filter
    have : ∀ (k l : Nat), k < l → k < (l.filter p).length → l < (l.filter p).length →
      ∃ (kp lp : Nat), kp < lp ∧ kp < l.length ∧ lp < l.length ∧
        (l.filter p)[k]! = l[kp]! ∧ (l.filter p)[l]! = l[lp]! := by
      intro k l hkl hk hl
      induction l using List.rec with
      | nil => simp at hk
      | cons head tail ih =>
        cases' decidable_eq_of_decidable (p head) with hp hnp
        · -- p head = true
          simp [List.filter_cons_of_pos hp] at hk hl
          cases' k with
          | zero => 
            cases' l with
            | zero => simp at hkl
            | succ l' =>
              simp at hl
              -- Continue with induction
              have : ∃ (kp lp : Nat), kp < lp ∧ kp < tail.length ∧ lp < tail.length ∧
                (tail.filter p)[k]! = tail[kp]! ∧ (tail.filter p)[l']! = tail[lp]! := by
                apply ih
                · exact Nat.lt_of_succ_lt_succ hkl
                · exact hk
                · exact hl
              obtain ⟨kp, lp, horder, hkp, hlp, heq_k, heq_l⟩ := this
              use kp + 1, lp + 1
              constructor
              · exact Nat.succ_lt_succ horder
              · constructor
                · exact Nat.succ_lt_succ hkp
                · constructor
                  · exact Nat.succ_lt_succ hlp
                  · constructor
                    · rw [List.filter_cons_of_pos hp]
                      simp [List.getElem!_cons_zero]
                      exact heq_k
                    · exact heq_l
          | succ k' =>
            cases' l with
            | zero => simp at hkl
            | succ l' =>
              simp [List.filter_cons_of_pos hp] at hk hl
              have : ∃ (kp lp : Nat), kp < lp ∧ kp < tail.length ∧ lp < tail.length ∧
                (tail.filter p)[k']! = tail[kp]! ∧ (tail.filter p)[l']! = tail[lp]! := by
                apply ih
                · exact Nat.lt_of_succ_lt_succ hkl
                · exact hk
                · exact hl
              obtain ⟨kp, lp, horder, hkp, hlp, heq_k, heq_l⟩ := this
              use kp + 1, lp + 1
              constructor
              · exact Nat.succ_lt_succ horder
              · constructor
                · exact Nat.succ_lt_succ hkp
                · constructor
                  · exact Nat.succ_lt_succ hlp
                  · constructor
                    · exact heq_k
                    · exact heq_l
        · -- p head = false
          simp [List.filter_cons_of_neg hnp] at hk hl
          have : ∃ (kp lp : Nat), kp < lp ∧ kp < tail.length ∧ lp < tail.length ∧
            (tail.filter p)[k]! = tail[kp]! ∧ (tail.filter p)[l]! = tail[lp]! := by
            apply ih
            · exact hkl
            · exact hk
            · exact hl
          obtain ⟨kp, lp, horder, hkp, hlp, heq_k, heq_l⟩ := this
          use kp + 1, lp + 1
          constructor
          · exact Nat.succ_lt_succ horder
          · constructor
            · exact Nat.succ_lt_succ hkp
            · constructor
              · exact Nat.succ_lt_succ hlp
              · constructor
                · exact heq_k
                · exact heq_l
    obtain ⟨_, _, order_prop, _, _, _, _⟩ := this i j hij hi hj
    exact order_prop
  
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
  obtain ⟨ip, jp, order, hip, hjp, heq_i, heq_j⟩ := filter_preserves_order numbers (fun x => numbers.count x = 1) i j hij hi hj
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