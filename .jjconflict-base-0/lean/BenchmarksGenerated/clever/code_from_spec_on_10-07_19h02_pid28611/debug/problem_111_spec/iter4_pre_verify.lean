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
def getMostFrequentChars (s: String) : Std.HashMap Char Nat :=
  let lowerChars := s.data.filter (fun c => c.isLower)
  if lowerChars.isEmpty then
    Std.HashMap.empty
  else
    let charCounts := lowerChars.map (fun c => (c, s.count c))
    let maxCount := charCounts.map (fun (_, count) => count) |>.maximum?
    match maxCount with
    | none => Std.HashMap.empty
    | some max => 
      let mostFrequent := charCounts.filter (fun (_, count) => count = max)
      mostFrequent.foldl (fun acc (char, count) => acc.insert char count) Std.HashMap.empty

def implementation (s: String) : Std.HashMap Char Nat := getMostFrequentChars s

-- LLM HELPER
lemma splitOn_space_length (s: String) : s.splitOn " " |>.all (fun c => c.length = 1) ↔ ∀ c ∈ s.data, c ≠ ' ' := by
  constructor
  · intro h
    intro c hc
    by_contra h_contra
    have : " " ∈ s.splitOn " " := by
      rw [String.mem_splitOn_iff]
      exact ⟨hc, h_contra⟩
    have : " ".length = 1 := h " " this
    simp at this
  · intro h
    intro part hpart
    by_contra h_contra
    have : part.length ≠ 1 := h_contra
    cases' Nat.lt_or_gt_of_ne this with h_lt h_gt
    · have : part.length = 0 := Nat.eq_zero_of_lt_one h_lt
      have : part = "" := String.eq_empty_of_length_eq_zero this
      rw [this] at hpart
      have : "" ∈ s.splitOn " " := hpart
      rw [String.mem_splitOn_iff] at this
      obtain ⟨_, h_eq⟩ := this
      simp at h_eq
    · have : part.length ≥ 2 := Nat.succ_le_of_lt h_gt
      have : ∃ c1 c2, c1 ∈ part.data ∧ c2 ∈ part.data ∧ c1 ≠ c2 := by
        have : part.data.length ≥ 2 := by simp [String.length_eq_data_length]; exact this
        cases' part.data with
        | nil => simp at this
        | cons c1 cs => 
          cases' cs with
          | nil => simp at this
          | cons c2 cs' => 
            exact ⟨c1, c2, List.mem_cons_self _ _, List.mem_cons_of_mem _ (List.mem_cons_self _ _), by simp⟩
      obtain ⟨c1, c2, hc1, hc2, hne⟩ := this
      have : c1 ∈ s.data := by
        rw [String.mem_splitOn_iff] at hpart
        obtain ⟨hsub, _⟩ := hpart
        exact hsub hc1
      have : c1 ≠ ' ' := h c1 this
      have : c2 ∈ s.data := by
        rw [String.mem_splitOn_iff] at hpart
        obtain ⟨hsub, _⟩ := hpart
        exact hsub hc2
      have : c2 ≠ ' ' := h c2 this
      rw [String.mem_splitOn_iff] at hpart
      obtain ⟨_, h_no_space⟩ := hpart
      exact h_no_space c1 hc1 rfl

def implementation (s: String) : Std.HashMap Char Nat := 
  let lowerChars := s.data.filter (fun c => c.isLower)
  if lowerChars.isEmpty then
    Std.HashMap.empty
  else
    let charCounts := lowerChars.map (fun c => (c, s.count c))
    let maxCount := (charCounts.map (fun (_, count) => count)).maximum?
    match maxCount with
    | none => Std.HashMap.empty
    | some max => 
      let mostFrequent := charCounts.filter (fun (_, count) => count = max)
      mostFrequent.foldl (fun acc (char, count) => acc.insert char count) Std.HashMap.empty

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
        · split at hkey
          · simp at hkey
          · simp [List.foldl] at hkey
            have : key ∈ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
              convert hkey
              simp
            simp at this
            obtain ⟨_, h_in, h_eq⟩ := this
            have : key ∈ (List.filter (fun c => c.isLower) s.data) := by
              simp at h_in
              exact h_in
            simp at this
            exact this.2
      · simp [implementation] at hkey
        split at hkey
        · simp at hkey
        · split at hkey
          · simp at hkey
          · simp [List.foldl] at hkey
            have : key ∈ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
              convert hkey
              simp
            simp at this
            obtain ⟨_, h_in, h_eq⟩ := this
            have : key ∈ (List.filter (fun c => c.isLower) s.data) := by
              simp at h_in
              exact h_in
            simp at this
            exact this.1
    · simp [implementation] at hkey ⊢
      split at hkey
      · simp at hkey
      · split at hkey
        · simp at hkey
        · simp [List.foldl] at hkey
          have : key ∈ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
            convert hkey
            simp
          simp at this
          obtain ⟨_, h_in, h_eq⟩ := this
          have : (key, s.count key) ∈ List.filter (fun x => x.2 = _) _ := by
            simp
            exact ⟨h_in, h_eq⟩
          rw [← h_eq]
          have : Std.HashMap.get! (List.foldl (fun acc x => Std.HashMap.insert acc x.1 x.2) Std.HashMap.empty (List.filter (fun x => x.2 = _) _)) key = s.count key := by
            simp [Std.HashMap.get!]
            rw [Std.HashMap.get_insert]
            simp
          exact this
  · intro char hchar hlower
    constructor
    · intro ⟨char2, hchar2, hlower2, hne, hcount⟩
      simp [implementation]
      split
      · simp
        rw [List.filter_eq_nil] at *
        have : char ∉ s.data := by
          intro h_in
          have := hlower
          have : ¬(char.isLower) := by simp at *; exact sorry
          contradiction
        exact this hchar
      · split
        · simp
        · simp [List.foldl]
          by_contra h_contra
          have : char ∈ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
            convert h_contra
            simp
          simp at this
          obtain ⟨_, h_in, h_eq⟩ := this
          have : s.count char = _ := h_eq
          have : s.count char2 = _ := by
            have : char2 ∈ (List.filter (fun c => c.isLower) s.data) := by
              simp
              exact ⟨hchar2, hlower2⟩
            have : (char2, s.count char2) ∈ List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data) := by
              simp
              exact this
            have : s.count char2 ∈ List.map (fun x => x.2) (List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data)) := by
              simp
              exact this
            have : s.count char2 ≤ (List.map (fun x => x.2) (List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data))).maximum? := by
              simp [List.maximum?]
              exact sorry
            rw [← this] at h_eq
            have : s.count char2 ≤ s.count char := by
              rw [h_eq]
              exact sorry
            linarith [hcount]
          exact sorry
    · intro h_not_in
      simp [implementation] at h_not_in
      split at h_not_in
      · simp at h_not_in
        rw [List.filter_eq_nil] at *
        have : char ∉ s.data := by
          intro h_in
          have : ¬(char.isLower) := by simp at *; exact sorry
          contradiction
        exact False.elim (this hchar)
      · split at h_not_in
        · simp at h_not_in
        · simp [List.foldl] at h_not_in
          have : char ∉ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
            convert h_not_in
            simp
          simp at this
          have : (char, s.count char) ∉ List.filter (fun x => x.2 = _) _ := by
            by_contra h_contra
            have : char ∈ (List.filter (fun x => x.2 = _) _).map Prod.fst := by
              simp
              exact ⟨char, h_contra, rfl⟩
            contradiction
          simp at this
          have : s.count char ≠ _ := this
          have : ∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧ s.count char < s.count char2 := by
            have : s.count char < _ := by
              have : char ∈ (List.filter (fun c => c.isLower) s.data) := by
                simp
                exact ⟨hchar, hlower⟩
              have : (char, s.count char) ∈ List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data) := by
                simp
                exact this
              have : s.count char ∈ List.map (fun x => x.2) (List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data)) := by
                simp
                exact this
              have : s.count char ≤ (List.map (fun x => x.2) (List.map (fun c => (c, s.count c)) (List.filter (fun c => c.isLower) s.data))).maximum? := by
                simp [List.maximum?]
                exact sorry
              have : s.count char ≠ _ := this
              exact sorry
            obtain ⟨char2, hchar2, hlower2, hne, hcount⟩ := sorry
            exact ⟨char2, hchar2, hlower2, hne, hcount⟩
          exact this