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
  if h : 1 ≤ x ∧ x ≤ 9 then
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
lemma intToString_in_digits (x: Int) (h: 1 ≤ x ∧ x ≤ 9) : 
  intToString x ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  unfold intToString
  simp [h]
  have : x.natAbs ≥ 1 := by
    cases' x with n n
    · simp [Int.natAbs]
      exact h.1
    · simp [Int.natAbs]
      have : Int.negSucc n ≤ 0 := Int.negSucc_lt_zero n
      have : 1 ≤ Int.negSucc n := h.1
      linarith
  have : x.natAbs ≤ 9 := by
    cases' x with n n
    · simp [Int.natAbs]
      exact h.2
    · simp [Int.natAbs]
      have : Int.negSucc n ≤ 0 := Int.negSucc_lt_zero n
      have : 1 ≤ Int.negSucc n := h.1
      linarith
  interval_cases x.natAbs <;> simp

-- LLM HELPER
lemma filterAndConvert_mem (arr: List Int) (s: String) :
  s ∈ filterAndConvert arr → s ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  intro h
  unfold filterAndConvert at h
  simp at h
  obtain ⟨x, hx1, hx2⟩ := h
  rw [←hx2]
  exact intToString_in_digits x hx1

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
          have h1 : x ∈ arr := hx.1
          have h2 : 1 ≤ x ∧ x ≤ 9 := ⟨hx.2.1, hx.2.2⟩
          have : intToString x ∈ filterAndConvert arr := by
            unfold filterAndConvert
            simp
            use x
            exact ⟨⟨h1, h2⟩, rfl⟩
          rw [sortByValue_mem]
          convert this
          unfold intToString
          simp [h2]
          have : x.natAbs = Int.natAbs x := rfl
          rw [this]
          have : Int.natAbs x ≥ 1 := by
            cases' x with n n
            · simp [Int.natAbs]
              exact h2.1
            · simp [Int.natAbs]
              have : Int.negSucc n ≤ 0 := Int.negSucc_lt_zero n
              have : 1 ≤ Int.negSucc n := h2.1
              linarith
          have : Int.natAbs x ≤ 9 := by
            cases' x with n n
            · simp [Int.natAbs]
              exact h2.2
            · simp [Int.natAbs]
              have : Int.negSucc n ≤ 0 := Int.negSucc_lt_zero n
              have : 1 ≤ Int.negSucc n := h2.1
              linarith
          interval_cases Int.natAbs x <;> simp
        · unfold sortByValue
          simp [List.Sorted]
          apply List.Sorted.of_mergeSort
          intro a b
          simp