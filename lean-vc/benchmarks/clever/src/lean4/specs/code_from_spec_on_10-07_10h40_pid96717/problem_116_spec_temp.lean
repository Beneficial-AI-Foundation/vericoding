import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  ∀ x : Nat, lst.count x = result.count x ∧
  result.length = lst.length ∧
  (∀ i j : Nat, i < j → j < result.length →
    Nat.digits 2 (result.get! i) < Nat.digits 2 (result.get! j) ∨
    (Nat.digits 2 (result.get! i) = Nat.digits 2 (result.get! j) ∧ result.get! i < result.get! j))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def bitLength (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def compareByBits (a b : Nat) : Bool :=
  let bitsA := Nat.digits 2 a
  let bitsB := Nat.digits 2 b
  if bitsA.length < bitsB.length then true
  else if bitsA.length > bitsB.length then false
  else a < b

-- LLM HELPER
def mergeSort (r : Nat → Nat → Bool) : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | l => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge r (mergeSort r left) (mergeSort r right)
where
  merge (r : Nat → Nat → Bool) : List Nat → List Nat → List Nat
    | [], ys => ys
    | xs, [] => xs
    | x :: xs, y :: ys =>
      if r x y then x :: merge r xs (y :: ys)
      else y :: merge r (x :: xs) ys

def implementation (lst: List Nat) : List Nat := 
  mergeSort compareByBits lst

-- LLM HELPER
lemma merge_length (r : Nat → Nat → Bool) : ∀ l1 l2 : List Nat, 
  (mergeSort.merge r l1 l2).length = l1.length + l2.length := by
  intro l1 l2
  induction l1 generalizing l2 with
  | nil => simp [mergeSort.merge]
  | cons a l1 ih =>
    induction l2 with
    | nil => simp [mergeSort.merge]
    | cons b l2 ih2 =>
      simp [mergeSort.merge]
      by_cases h : r a b
      · simp [h]
        rw [ih]
        simp
      · simp [h]
        rw [ih2]
        simp [Nat.add_assoc, Nat.add_comm 1]

-- LLM HELPER
lemma mergeSort_length : ∀ r : Nat → Nat → Bool, ∀ l : List Nat, 
  (mergeSort r l).length = l.length := by
  intro r l
  induction l using List.strongInductionOn with
  | ind l ih =>
    cases l with
    | nil => simp [mergeSort]
    | cons a l' =>
      cases l' with
      | nil => simp [mergeSort]
      | cons b l'' =>
        simp [mergeSort]
        let full := a :: b :: l''
        let mid := full.length / 2
        let left := full.take mid
        let right := full.drop mid
        rw [merge_length]
        have h1 : left.length < full.length := by
          simp [left, full]
          exact List.length_take_le_length full mid
        have h2 : right.length < full.length := by
          simp [right, full]
          sorry
        rw [ih left h1, ih right h2]
        rw [List.length_take, List.length_drop]
        simp [full]
        sorry

-- LLM HELPER  
lemma merge_count (r : Nat → Nat → Bool) : ∀ l1 l2 : List Nat, ∀ x : Nat,
  (mergeSort.merge r l1 l2).count x = l1.count x + l2.count x := by
  intro l1 l2 x
  induction l1 generalizing l2 with
  | nil => simp [mergeSort.merge]
  | cons a l1 ih =>
    induction l2 with
    | nil => simp [mergeSort.merge]
    | cons b l2 ih2 =>
      simp [mergeSort.merge]
      by_cases h : r a b
      · simp [h]
        rw [ih]
        simp [List.count_cons]
        by_cases h' : a = x
        · simp [h']
        · simp [h']
      · simp [h]
        rw [ih2]
        simp [List.count_cons]
        by_cases h' : b = x
        · simp [h']
          rw [Nat.add_assoc, Nat.add_comm (l1.count x), Nat.add_assoc]
        · simp [h']

-- LLM HELPER
lemma mergeSort_count : ∀ r : Nat → Nat → Bool, ∀ l : List Nat, ∀ x : Nat,
  (mergeSort r l).count x = l.count x := by
  intro r l x
  induction l using List.strongInductionOn with
  | ind l ih =>
    cases l with
    | nil => simp [mergeSort]
    | cons a l' =>
      cases l' with
      | nil => simp [mergeSort]
      | cons b l'' =>
        simp [mergeSort]
        let full := a :: b :: l''
        let mid := full.length / 2
        let left := full.take mid
        let right := full.drop mid
        rw [merge_count]
        have h1 : left.length < full.length := by
          simp [left, full]
          exact List.length_take_le_length full mid
        have h2 : right.length < full.length := by
          simp [right, full]
          sorry
        rw [ih left h1, ih right h2]
        rw [List.count_take, List.count_drop]
        sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  simp
  let result := mergeSort compareByBits lst
  use result
  constructor
  · rfl
  · intro x
    constructor
    · exact mergeSort_count compareByBits lst x
    · constructor
      · exact mergeSort_length compareByBits lst
      · intro i j hij hjlen
        sorry