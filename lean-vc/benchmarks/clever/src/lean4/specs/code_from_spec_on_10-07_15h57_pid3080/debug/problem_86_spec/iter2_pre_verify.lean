import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  result.length = s.length ∧
  let words := result.split (fun c => c = ' ');
  let s_words := s.split (fun c => c = ' ');
  s_words.length = words.length ∧
  ∀ i, i < words.length →
    words[i]!.length = s_words[i]!.length ∧
    ((∀ j, j < words[i]!.length →
      (words[i]!.data[j]! ∈ s_words[i]!.data ∧
      s_words[i]!.data[j]! ∈ words[i]!.data ∧
      words[i]!.data.count (words[i]!.data[j]!) = s_words[i]!.data.count (s_words[i]!.data[j]!))) ∧
    List.Sorted Nat.le (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def List.mergeSort {α : Type*} (l : List α) (le : α → α → Bool) : List α :=
  match l with
  | [] => []
  | [a] => [a]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sortedLeft := left.mergeSort le
    let sortedRight := right.mergeSort le
    merge sortedLeft sortedRight le
where
  merge : List α → List α → (α → α → Bool) → List α
  | [], r, _ => r
  | l, [], _ => l
  | a::as, b::bs, le => 
    if le a b then a :: merge as (b::bs) le
    else b :: merge (a::as) bs le

-- LLM HELPER
def sortStringChars (s: String) : String :=
  let chars := s.data
  let sortedChars := chars.mergeSort (fun a b => a.val.toNat ≤ b.val.toNat)
  ⟨sortedChars⟩

-- LLM HELPER
def processWords (words: List String) : List String :=
  words.map sortStringChars

-- LLM HELPER
def joinWords (words: List String) : String :=
  match words with
  | [] => ""
  | [w] => w
  | w :: ws => w ++ " " ++ joinWords ws

def implementation (s: String) : String := 
  let words := s.split (fun c => c = ' ')
  let sortedWords := processWords words
  joinWords sortedWords

-- LLM HELPER
lemma List.length_mergeSort {α : Type*} (l : List α) (le : α → α → Bool) : 
  (l.mergeSort le).length = l.length := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    cases l with
    | nil => simp [List.mergeSort]
    | cons a as =>
      cases as with
      | nil => simp [List.mergeSort]
      | cons b bs =>
        simp [List.mergeSort]
        have h1 : (a :: b :: bs).take ((a :: b :: bs).length / 2) ++ (a :: b :: bs).drop ((a :: b :: bs).length / 2) = a :: b :: bs := List.take_append_drop _ _
        have h2 : ((a :: b :: bs).take ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_take]
          apply Nat.min_lt_iff.mpr
          left
          simp
        have h3 : ((a :: b :: bs).drop ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_drop]
          apply Nat.sub_lt
          · simp
          · simp [Nat.div_pos]
        rw [←merge_length]
        · rw [ih _ h2, ih _ h3]
          rw [List.length_take, List.length_drop]
          simp
        · exact (a :: b :: bs).take ((a :: b :: bs).length / 2)
        · exact (a :: b :: bs).drop ((a :: b :: bs).length / 2)
        · exact le
where
  merge_length {α : Type*} : ∀ (l1 l2 : List α) (le : α → α → Bool), 
    (List.mergeSort.merge l1 l2 le).length = l1.length + l2.length
  | [], l2, _ => by simp [List.mergeSort.merge]
  | l1, [], _ => by simp [List.mergeSort.merge]
  | a::as, b::bs, le => by
    simp [List.mergeSort.merge]
    split
    · simp [merge_length as (b::bs) le]
    · simp [merge_length (a::as) bs le]

-- LLM HELPER
lemma sortStringChars_length (s: String) : (sortStringChars s).length = s.length := by
  simp [sortStringChars, String.length]
  rw [List.length_mergeSort]

-- LLM HELPER
lemma List.Perm.mergeSort {α : Type*} (l : List α) (le : α → α → Bool) : 
  l.mergeSort le ~ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    cases l with
    | nil => simp [List.mergeSort]
    | cons a as =>
      cases as with
      | nil => simp [List.mergeSort]
      | cons b bs =>
        simp [List.mergeSort]
        have h1 : (a :: b :: bs).take ((a :: b :: bs).length / 2) ++ (a :: b :: bs).drop ((a :: b :: bs).length / 2) = a :: b :: bs := List.take_append_drop _ _
        have h2 : ((a :: b :: bs).take ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_take]
          apply Nat.min_lt_iff.mpr
          left
          simp
        have h3 : ((a :: b :: bs).drop ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_drop]
          apply Nat.sub_lt
          · simp
          · simp [Nat.div_pos]
        have perm_left := ih _ h2
        have perm_right := ih _ h3
        have merge_perm := merge_preserves_perm perm_left perm_right le
        rw [←h1] at merge_perm
        exact merge_perm.trans (List.perm_append_comm _ _).symm
where
  merge_preserves_perm {α : Type*} : ∀ {l1 l2 : List α} {l1' l2' : List α} (le : α → α → Bool),
    l1 ~ l1' → l2 ~ l2' → List.mergeSort.merge l1 l2 le ~ l1' ++ l2'
  | [], l2, [], l2', le, h1, h2 => by simp [List.mergeSort.merge]; exact h2
  | l1, [], l1', [], le, h1, h2 => by simp [List.mergeSort.merge]; exact h1
  | a::as, b::bs, l1', l2', le, h1, h2 => by
    simp [List.mergeSort.merge]
    split
    · have : List.mergeSort.merge as (b::bs) le ~ List.tail l1' ++ l2' := by
        apply merge_preserves_perm le
        · exact List.perm_of_cons_perm h1
        · exact h2
      constructor
      · exact List.perm_head_of_perm h1
      · exact this
    · have : List.mergeSort.merge (a::as) bs le ~ l1' ++ List.tail l2' := by
        apply merge_preserves_perm le
        · exact h1
        · exact List.perm_of_cons_perm h2
      rw [List.cons_append]
      constructor
      · exact List.perm_head_of_perm h2
      · exact this

-- LLM HELPER
lemma sortStringChars_data_perm (s: String) : 
  (sortStringChars s).data ~ s.data := by
  simp [sortStringChars]
  exact List.Perm.mergeSort _ _

-- LLM HELPER
lemma List.Sorted.mergeSort {α : Type*} [LinearOrder α] (l : List α) : 
  List.Sorted (· ≤ ·) (l.mergeSort (fun a b => a ≤ b)) := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    cases l with
    | nil => simp [List.mergeSort, List.Sorted]
    | cons a as =>
      cases as with
      | nil => simp [List.mergeSort, List.Sorted]
      | cons b bs =>
        simp [List.mergeSort]
        have h1 : ((a :: b :: bs).take ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_take]
          apply Nat.min_lt_iff.mpr
          left
          simp
        have h2 : ((a :: b :: bs).drop ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
          simp [List.length_drop]
          apply Nat.sub_lt
          · simp
          · simp [Nat.div_pos]
        have sorted_left := ih _ h1
        have sorted_right := ih _ h2
        exact merge_sorted sorted_left sorted_right
where
  merge_sorted {α : Type*} [LinearOrder α] : ∀ (l1 l2 : List α),
    List.Sorted (· ≤ ·) l1 → List.Sorted (· ≤ ·) l2 → List.Sorted (· ≤ ·) (List.mergeSort.merge l1 l2 (fun a b => a ≤ b))
  | [], l2, _, h2 => by simp [List.mergeSort.merge]; exact h2
  | l1, [], h1, _ => by simp [List.mergeSort.merge]; exact h1
  | a::as, b::bs, h1, h2 => by
    simp [List.mergeSort.merge]
    split
    · exact List.Sorted.cons (List.sorted_head_of_sorted h1) (merge_sorted as (b::bs) (List.sorted_tail_of_sorted h1) h2)
    · exact List.Sorted.cons (List.sorted_head_of_sorted h2) (merge_sorted (a::as) bs h1 (List.sorted_tail_of_sorted h2))

-- LLM HELPER
lemma sortStringChars_sorted (s: String) : 
  List.Sorted Nat.le ((sortStringChars s).data.map (fun c => c.val.toNat)) := by
  simp [sortStringChars]
  apply List.Sorted.map
  · exact fun _ _ => id
  · have : List.Sorted (· ≤ ·) (s.data.mergeSort (fun a b => a.val.toNat ≤ b.val.toNat)) := by
      induction s.data using List.strongInductionOn with
      | ind l ih =>
        cases l with
        | nil => simp [List.mergeSort, List.Sorted]
        | cons a as =>
          cases as with
          | nil => simp [List.mergeSort, List.Sorted]
          | cons b bs =>
            simp [List.mergeSort]
            have h1 : ((a :: b :: bs).take ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
              simp [List.length_take]
              apply Nat.min_lt_iff.mpr
              left
              simp
            have h2 : ((a :: b :: bs).drop ((a :: b :: bs).length / 2)).length < (a :: b :: bs).length := by
              simp [List.length_drop]
              apply Nat.sub_lt
              · simp
              · simp [Nat.div_pos]
            have sorted_left := ih _ h1
            have sorted_right := ih _ h2
            exact merge_sorted sorted_left sorted_right
    exact this
where
  merge_sorted : ∀ (l1 l2 : List Char),
    List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) l1 → 
    List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) l2 → 
    List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) (List.mergeSort.merge l1 l2 (fun a b => a.val.toNat ≤ b.val.toNat))
  | [], l2, _, h2 => by simp [List.mergeSort.merge]; exact h2
  | l1, [], h1, _ => by simp [List.mergeSort.merge]; exact h1
  | a::as, b::bs, h1, h2 => by
    simp [List.mergeSort.merge]
    split
    · exact List.Sorted.cons (List.sorted_head_of_sorted h1) (merge_sorted as (b::bs) (List.sorted_tail_of_sorted h1) h2)
    · exact List.Sorted.cons (List.sorted_head_of_sorted h2) (merge_sorted (a::as) bs h1 (List.sorted_tail_of_sorted h2))

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp only [implementation]
    constructor
    · -- result.length = s.length
      have h1 : (joinWords (processWords (s.split (fun c => c = ' ')))).length = s.length := by
        induction s.split (fun c => c = ' ') with
        | nil => simp [joinWords, processWords]
        | cons w ws ih =>
          simp [joinWords, processWords]
          cases ws with
          | nil => 
            simp [joinWords]
            exact sortStringChars_length w
          | cons w' ws' =>
            simp [joinWords]
            rw [String.length_append, String.length_append]
            simp
            have : (sortStringChars w).length = w.length := sortStringChars_length w
            rw [this]
            have : (joinWords (processWords (w' :: ws'))).length = (String.join " " (w' :: ws')).length := by
              rw [ih]
              simp
            rw [this]
            simp
      exact h1
    · constructor
      · -- word count preservation
        simp [processWords]
        rw [List.length_map]
      · -- main property for each word
        intro i hi
        simp [processWords]
        rw [List.getElem_map]
        constructor
        · -- length preservation
          exact sortStringChars_length _
        · constructor
          · -- character membership and count preservation
            intro j hj
            have perm := sortStringChars_data_perm (s.split (fun c => c = ' '))[i]!
            constructor
            · exact List.Perm.mem_iff perm.symm |>.mpr
            · constructor
              · exact List.Perm.mem_iff perm |>.mpr
              · exact List.Perm.count_eq perm
          · -- sorting property
            exact sortStringChars_sorted _