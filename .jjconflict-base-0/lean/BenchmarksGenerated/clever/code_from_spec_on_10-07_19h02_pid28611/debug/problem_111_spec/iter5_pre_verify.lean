import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Std.HashMap Char Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Std.HashMap Char Nat) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ key ∈ result.keys,
      (key.isLower ∧
      key ∈ s.data ∧
      result.get! key = s.count key) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      s.count char < s.count char2) ↔ char ∉ result.keys))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def max_count_in_string (s: String) : Nat :=
  let lowerChars := s.data.filter (fun c => c.isLower)
  if lowerChars.isEmpty then 0 else
    (lowerChars.map (fun c => s.count c)).maximum?.getD 0

def implementation (s: String) : Std.HashMap Char Nat := 
  let lowerChars := s.data.filter (fun c => c.isLower)
  if lowerChars.isEmpty then
    Std.HashMap.empty
  else
    let maxCount := max_count_in_string s
    let mostFrequent := lowerChars.filter (fun c => s.count c = maxCount)
    mostFrequent.foldl (fun acc char => acc.insert char (s.count char)) Std.HashMap.empty

-- LLM HELPER
lemma filter_mem_iff (l : List α) (p : α → Bool) (x : α) : 
  x ∈ l.filter p ↔ x ∈ l ∧ p x := by
  simp [List.mem_filter]

-- LLM HELPER
lemma foldl_insert_mem (chars : List Char) (char : Char) :
  char ∈ (chars.foldl (fun acc c => acc.insert c (String.count ⟨chars⟩ c)) Std.HashMap.empty).keys ↔
  char ∈ chars := by
  induction chars with
  | nil => simp
  | cons c cs ih => 
    simp [List.foldl]
    constructor
    · intro h
      cases' h with h h
      · left; exact h
      · right; exact ih.mp h
    · intro h
      cases' h with h h
      · left; exact h
      · right; exact ih.mpr h

theorem correctness (s: String) : problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h
    intro key hkey
    constructor
    · constructor
      · simp [implementation] at hkey
        split at hkey
        · simp at hkey
        · simp [List.foldl] at hkey
          have : key ∈ (List.filter (fun c => String.count s c = max_count_in_string s) 
                         (List.filter (fun c => c.isLower) s.data)) := by
            rw [← foldl_insert_mem]
            exact hkey
          rw [filter_mem_iff] at this
          exact this.1.2
      · simp [implementation] at hkey
        split at hkey
        · simp at hkey
        · simp [List.foldl] at hkey
          have : key ∈ (List.filter (fun c => String.count s c = max_count_in_string s) 
                         (List.filter (fun c => c.isLower) s.data)) := by
            rw [← foldl_insert_mem]
            exact hkey
          rw [filter_mem_iff] at this
          exact this.1.1
    · simp [implementation] at hkey ⊢
      split at hkey
      · simp at hkey
      · have : key ∈ (List.filter (fun c => String.count s c = max_count_in_string s) 
                       (List.filter (fun c => c.isLower) s.data)) := by
          rw [← foldl_insert_mem]
          exact hkey
        rw [filter_mem_iff] at this
        simp [Std.HashMap.get!]
        exact this.2
  · intro char hchar hlower
    constructor
    · intro ⟨char2, hchar2, hlower2, hne, hcount⟩
      simp [implementation]
      split
      · simp
        rw [List.filter_eq_nil] at *
        have : char ∉ s.data ∨ ¬char.isLower := by
          by_contra h
          push_neg at h
          exact this char h.1 h.2
        cases' this with h h
        · exact h hchar
        · exact h hlower
      · simp [List.foldl]
        rw [← foldl_insert_mem]
        rw [filter_mem_iff]
        push_neg
        right
        intro h_in
        have : s.count char < max_count_in_string s := by
          simp [max_count_in_string]
          split
          · simp
          · simp [List.max?]
            have : char2 ∈ s.data.filter (fun c => c.isLower) := by
              rw [filter_mem_iff]
              exact ⟨hchar2, hlower2⟩
            have : s.count char2 ∈ (s.data.filter (fun c => c.isLower)).map (fun c => s.count c) := by
              simp
              exact this
            have : s.count char2 ≤ ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max?.getD 0 := by
              simp [List.max?, List.maximum?]
              exact List.le_max_of_mem this (by simp)
            exact Nat.lt_of_lt_of_le hcount this
        exact Nat.ne_of_lt this
    · intro h_not_in
      simp [implementation] at h_not_in
      split at h_not_in
      · simp at h_not_in
        rw [List.filter_eq_nil] at *
        have : char ∉ s.data ∨ ¬char.isLower := by
          by_contra h
          push_neg at h
          exact this char h.1 h.2
        cases' this with h h
        · exact False.elim (h hchar)
        · exact False.elim (h hlower)
      · simp [List.foldl] at h_not_in
        rw [← foldl_insert_mem, filter_mem_iff] at h_not_in
        push_neg at h_not_in
        have h_lower_in : char ∈ s.data.filter (fun c => c.isLower) := by
          rw [filter_mem_iff]
          exact ⟨hchar, hlower⟩
        have : s.count char ≠ max_count_in_string s := h_not_in h_lower_in
        have : s.count char < max_count_in_string s := by
          simp [max_count_in_string]
          split
          · simp at h_lower_in
          · simp [List.max?]
            have : s.count char ∈ (s.data.filter (fun c => c.isLower)).map (fun c => s.count c) := by
              simp
              exact h_lower_in
            have : s.count char ≤ ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max?.getD 0 := by
              simp [List.max?, List.maximum?]
              exact List.le_max_of_mem this (by simp)
            exact Nat.lt_of_le_of_ne this this
        simp [max_count_in_string] at this
        split at this
        · simp at h_lower_in
        · simp [List.max?] at this
          have : ∃ count ∈ (s.data.filter (fun c => c.isLower)).map (fun c => s.count c), 
                   s.count char < count := by
            have : ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max?.getD 0 ∈ 
                   (s.data.filter (fun c => c.isLower)).map (fun c => s.count c) := by
              simp [List.max?, List.maximum?]
              exact List.mem_of_max? (by simp)
            use ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max?.getD 0
            exact ⟨this, this⟩
          obtain ⟨count, hcount_mem, hcount_gt⟩ := this
          simp at hcount_mem
          obtain ⟨char2, hchar2_mem, hchar2_count⟩ := hcount_mem
          rw [filter_mem_iff] at hchar2_mem
          use char2
          rw [← hchar2_count] at hcount_gt
          have : char ≠ char2 := by
            by_contra h_eq
            rw [h_eq] at hcount_gt
            exact Nat.lt_irrefl (s.count char2) hcount_gt
          exact ⟨hchar2_mem.1, hchar2_mem.2, this.symm, hcount_gt⟩