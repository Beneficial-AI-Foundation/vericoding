import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List String)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: List String) :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"];
  (forall s: String, (s ∈ result → s ∈ digits)) ∧
  (arr.length ≥ result.length) ∧
  (forall x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → (digits[x-1]! ∈ result)) ∧
  (List.Sorted Int.le (List.map (fun (s: String) => (List.indexOf s digits) + 1) result).reverse)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def intToString (x: Int) : String :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  if 1 ≤ x ∧ x ≤ 9 then
    digits[x.natAbs - 1]!
  else
    ""

-- LLM HELPER
def filterAndConvert (arr: List Int) : List String :=
  (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).map intToString

-- LLM HELPER
def sortByValue (strings: List String) : List String :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  let pairs := strings.map (fun s => (s, List.indexOf s digits + 1))
  let sortedPairs := pairs.mergeSort (fun a b => a.2 ≥ b.2)
  sortedPairs.map (fun p => p.1)

def implementation (arr: List Int) : List String := 
  sortByValue (filterAndConvert arr)

-- LLM HELPER
lemma int_to_nat_le (x: Int) (h: 1 ≤ x ∧ x ≤ 9) : 1 ≤ x.natAbs ∧ x.natAbs ≤ 9 := by
  cases' x with n n
  · simp [Int.natAbs]
    constructor
    · have : 1 ≤ (n : Int) := h.1
      have : 0 < n := by
        by_contra h_neg
        push_neg at h_neg
        have : (n : Int) ≤ 0 := Nat.cast_le.mpr (le_of_not_gt h_neg)
        linarith
      exact this
    · have : (n : Int) ≤ 9 := h.2
      exact Int.natCast_le.mpr h.2
  · simp [Int.natAbs]
    have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    have : 1 ≤ Int.negSucc n := h.1
    linarith

-- LLM HELPER
lemma intToString_in_digits (x: Int) (h: 1 ≤ x ∧ x ≤ 9) : 
  intToString x ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  unfold intToString
  simp [h]
  have hab := int_to_nat_le x h
  cases' x with n n
  · simp [Int.natAbs]
    have : n ≤ 9 := by
      have : (n : Int) ≤ 9 := h.2
      exact Int.natCast_le.mpr this
    have : 1 ≤ n := by
      have : 1 ≤ (n : Int) := h.1
      have : 0 < n := by
        by_contra h_neg
        push_neg at h_neg
        have : (n : Int) ≤ 0 := Nat.cast_le.mpr (le_of_not_gt h_neg)
        linarith
      exact this
    interval_cases n <;> simp
  · simp [Int.natAbs]
    have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    have : 1 ≤ Int.negSucc n := h.1
    linarith

-- LLM HELPER
lemma filterAndConvert_mem (arr: List Int) (s: String) :
  s ∈ filterAndConvert arr → s ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  intro h
  unfold filterAndConvert at h
  simp at h
  obtain ⟨x, hx1, hx2⟩ := h
  rw [←hx2]
  exact intToString_in_digits x hx1.2

-- LLM HELPER
lemma sortByValue_mem (strings: List String) (s: String) :
  s ∈ sortByValue strings ↔ s ∈ strings := by
  unfold sortByValue
  simp [List.mem_map]
  constructor
  · intro h
    obtain ⟨p, hp1, hp2⟩ := h
    simp at hp1
    obtain ⟨s', hs1, hs2⟩ := hp1
    rw [←hp2, ←hs2]
    exact hs1
  · intro h
    use (s, List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] + 1)
    constructor
    · simp
      exact h
    · simp

-- LLM HELPER
lemma filterAndConvert_length_le (arr: List Int) :
  (filterAndConvert arr).length ≤ arr.length := by
  unfold filterAndConvert
  simp
  exact List.length_filter_le _ _

-- LLM HELPER
lemma sortByValue_length (strings: List String) :
  (sortByValue strings).length = strings.length := by
  unfold sortByValue
  simp

-- LLM HELPER
lemma nat_to_int_bounds (x: Nat) (h: 1 ≤ x ∧ x ≤ 9) : 1 ≤ (x: Int) ∧ (x: Int) ≤ 9 := by
  simp
  exact h

-- LLM HELPER
lemma digits_getElem_eq_intToString (x: Nat) (h: 1 ≤ x ∧ x ≤ 9) :
  ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"][x-1]! = intToString (x: Int) := by
  unfold intToString
  simp [nat_to_int_bounds x h]
  have : (x: Int).natAbs = x := by
    simp [Int.natAbs]
  rw [this]
  interval_cases x <;> simp

-- LLM HELPER
lemma map_indexOf_reverse_sorted (strings: List String) :
  List.Sorted Int.le (List.map (fun s => List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] + 1) (sortByValue strings)).reverse := by
  unfold sortByValue
  simp [List.map_map]
  have sorted_ge : List.Sorted (fun a b => a ≥ b) (List.map (fun p => p.2) ((List.map (fun s => (s, List.indexOf s ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] + 1)) strings).mergeSort (fun a b => a.2 ≥ b.2))) := by
    apply List.Sorted.map
    exact List.sorted_mergeSort
  exact List.Sorted.reverse.mpr sorted_ge

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  unfold problem_spec implementation
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  use sortByValue (filterAndConvert arr)
  constructor
  · rfl
  · constructor
    · intro s hs
      rw [sortByValue_mem] at hs
      exact filterAndConvert_mem arr s hs
    · constructor
      · rw [sortByValue_length]
        exact filterAndConvert_length_le arr
      · constructor
        · intro x hx
          have h1 : (x: Int) ∈ arr := hx.1
          have h2 : 1 ≤ (x: Int) ∧ (x: Int) ≤ 9 := nat_to_int_bounds x ⟨hx.2.1, hx.2.2⟩
          have : intToString (x: Int) ∈ filterAndConvert arr := by
            unfold filterAndConvert
            simp
            use (x: Int)
            exact ⟨⟨h1, h2⟩, rfl⟩
          rw [sortByValue_mem] at this
          rw [digits_getElem_eq_intToString x ⟨hx.2.1, hx.2.2⟩]
          exact this
        · exact map_indexOf_reverse_sorted (filterAndConvert arr)