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
    (lowerChars.map (fun c => s.count c)).max?.getD 0

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
lemma Std.HashMap.empty_keys : (Std.HashMap.empty : Std.HashMap Char Nat).keys = [] := by
  rfl

-- LLM HELPER
lemma Std.HashMap.mem_keys_insert (m : Std.HashMap Char Nat) (k : Char) (v : Nat) (c : Char) :
  c ∈ (m.insert k v).keys ↔ c = k ∨ c ∈ m.keys := by
  simp [Std.HashMap.mem_keys, Std.HashMap.contains_def]

-- LLM HELPER
lemma List.mem_keys_foldl_insert (chars : List Char) (s : String) (c : Char) :
  c ∈ (chars.foldl (fun acc c => acc.insert c (s.count c)) Std.HashMap.empty).keys ↔ c ∈ chars := by
  induction chars with
  | nil => 
    simp [List.foldl, Std.HashMap.empty_keys]
  | cons h t ih =>
    simp [List.foldl]
    constructor
    · intro hc
      by_cases h_eq : c = h
      · left
        exact h_eq.symm
      · right
        rw [← ih]
        have : c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) (Std.HashMap.empty.insert h (s.count h)) t).keys := by
          convert hc
          simp [List.foldl]
        have : c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) Std.HashMap.empty t).keys := by
          have fold_prop : ∀ (init : Std.HashMap Char Nat), 
            c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) init t).keys ↔ 
            c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) Std.HashMap.empty t).keys ∨ c ∈ init.keys := by
            intro init
            induction t generalizing init with
            | nil => simp [List.foldl]
            | cons h' t' ih' =>
              simp [List.foldl]
              rw [ih', ih']
              simp [Std.HashMap.mem_keys_insert, Std.HashMap.empty_keys]
              tauto
          rw [fold_prop] at this
          simp [Std.HashMap.mem_keys_insert, Std.HashMap.empty_keys] at this
          cases this with
          | inl h1 => exact h1
          | inr h2 => cases h2 with
            | inl h3 => exact False.elim (h_eq h3)
            | inr h4 => exact False.elim h4
        rw [ih] at this
        exact this
    · intro hc
      cases hc with
      | inl h_eq => 
        rw [← h_eq]
        have fold_prop : ∀ (init : Std.HashMap Char Nat), 
          h ∈ init.keys → 
          h ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) init t).keys := by
          intro init h_in_init
          induction t generalizing init with
          | nil => simp [List.foldl]; exact h_in_init
          | cons h' t' ih' =>
            simp [List.foldl]
            apply ih'
            simp [Std.HashMap.mem_keys_insert]
            right
            exact h_in_init
        apply fold_prop
        simp [Std.HashMap.mem_keys_insert, Std.HashMap.empty_keys]
      | inr h_in_t =>
        have fold_prop : ∀ (init : Std.HashMap Char Nat), 
          c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) Std.HashMap.empty t).keys → 
          c ∈ (List.foldl (fun acc c => acc.insert c (s.count c)) init t).keys := by
          intro init h_in_empty
          induction t generalizing init with
          | nil => simp [List.foldl] at h_in_empty; exact False.elim h_in_empty
          | cons h' t' ih' =>
            simp [List.foldl]
            apply ih'
            simp [List.foldl] at h_in_empty
            exact h_in_empty
        apply fold_prop
        rw [ih]
        exact h_in_t

theorem correctness (s: String) : problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h
    constructor
    · intro key hkey
      constructor
      · constructor
        · simp [implementation] at hkey
          split at hkey
          · simp at hkey
          · simp at hkey ⊢
            have : key ∈ (s.data.filter (fun c => c.isLower)).filter (fun c => s.count c = max_count_in_string s) := by
              simp [List.mem_keys_foldl_insert] at hkey
              exact hkey
            rw [List.mem_filter] at this
            exact this.1.2
        · simp [implementation] at hkey
          split at hkey
          · simp at hkey
          · simp at hkey ⊢
            have : key ∈ (s.data.filter (fun c => c.isLower)).filter (fun c => s.count c = max_count_in_string s) := by
              simp [List.mem_keys_foldl_insert] at hkey
              exact hkey
            rw [List.mem_filter] at this
            exact this.1.1
      · simp [implementation] at hkey ⊢
        split at hkey
        · simp at hkey
        · simp at hkey
          have : key ∈ (s.data.filter (fun c => c.isLower)).filter (fun c => s.count c = max_count_in_string s) := by
            simp [List.mem_keys_foldl_insert] at hkey
            exact hkey
          rw [List.mem_filter] at this
          simp [Std.HashMap.get!]
          have : s.count key = max_count_in_string s := this.2
          rw [List.mem_keys_foldl_insert] at hkey
          simp [Std.HashMap.get!]
          rfl
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
        · simp
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
                simp [List.max?]
                cases' h_max : ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max? with
                | none => simp at h_max; simp [List.map_eq_nil] at h_max; rw [List.filter_eq_nil] at h_max; simp at this
                | some val => simp; exact List.le_max_of_mem this val (by simp [List.max?]; rw [h_max]; simp)
              exact Nat.lt_of_lt_of_le hcount this
          have : char ∈ (s.data.filter (fun c => c.isLower)).filter (fun c => s.count c = max_count_in_string s) := by
            simp [List.mem_keys_foldl_insert] at h_in
            exact h_in
          rw [List.mem_filter] at this
          have : s.count char = max_count_in_string s := this.2
          rw [this] at this
          exact Nat.lt_irrefl (max_count_in_string s) this
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
        · simp at h_not_in
          have h_lower_in : char ∈ s.data.filter (fun c => c.isLower) := by
            rw [filter_mem_iff]
            exact ⟨hchar, hlower⟩
          have : char ∉ (s.data.filter (fun c => c.isLower)).filter (fun c => s.count c = max_count_in_string s) := by
            simp [List.mem_keys_foldl_insert] at h_not_in
            exact h_not_in
          rw [List.mem_filter] at this
          push_neg at this
          have : s.count char ≠ max_count_in_string s := this h_lower_in
          have : s.count char < max_count_in_string s := by
            simp [max_count_in_string]
            split
            · simp at h_lower_in
            · simp [List.max?]
              have : s.count char ∈ (s.data.filter (fun c => c.isLower)).map (fun c => s.count c) := by
                simp
                exact h_lower_in
              have : s.count char ≤ ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max?.getD 0 := by
                simp [List.max?]
                cases' h_max : ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max? with
                | none => simp at h_max; simp [List.map_eq_nil] at h_max; rw [List.filter_eq_nil] at h_max; simp at this
                | some val => simp; exact List.le_max_of_mem this val (by simp [List.max?]; rw [h_max]; simp)
              exact Nat.lt_of_le_of_ne this this
          simp [max_count_in_string] at this
          split at this
          · simp at h_lower_in
          · simp [List.max?] at this
            have : ∃ count ∈ (s.data.filter (fun c => c.isLower)).map (fun c => s.count c), 
                     s.count char < count := by
              cases' h_max : ((s.data.filter (fun c => c.isLower)).map (fun c => s.count c)).max? with
              | none => simp at h_max; simp [List.map_eq_nil] at h_max; rw [List.filter_eq_nil] at h_max; simp at h_lower_in
              | some val => 
                use val
                constructor
                · exact List.mem_of_max? h_max
                · exact this
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