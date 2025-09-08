/-
In this kata, your task is to identify the pattern underlying a sequence of numbers. For example, if the sequence is [1, 2, 3, 4, 5], then the pattern is [1], since each number in the sequence is equal to the number preceding it, plus 1. See the test cases for more examples.

A few more rules :

pattern may contain negative numbers.
sequence will always be made of a whole number of repetitions of the pattern.
Your answer must correspond to the shortest form of the pattern, e.g. if the pattern is [1], then [1, 1, 1, 1] will not be considered a correct answer.
-/

-- <vc-helpers>
-- </vc-helpers>

def findPattern (sequence : List Int) : Option (List Int) := sorry

def differencesSeq (sequence : List Int) : List Int :=
  (sequence.zip (sequence.drop 1)).map (fun (x, y) => y - x)

theorem valid_differences_pattern (sequence : List Int) (h : sequence.length ≥ 2) : 
  match findPattern sequence with
  | none => True 
  | some pattern =>
    let diffs := differencesSeq sequence
    -- Pattern length divides sequence length
    diffs.length % pattern.length = 0 ∧
    -- Pattern matches when repeated
    let repeatedPattern := List.replicate (diffs.length / pattern.length) pattern |>.join
    List.zip diffs repeatedPattern |>.all (fun (a, b) => a = b)
  := sorry

theorem minimal_pattern (sequence : List Int) (h : sequence.length ≥ 2) :
  match findPattern sequence with
  | none => True
  | some pattern =>
    let diffs := differencesSeq sequence
    ∀ i : Nat, 1 ≤ i → i < pattern.length → diffs.length % i = 0 →
      let shortPattern := diffs.take i
      let repeatedShortPattern := List.replicate (diffs.length / i) shortPattern |>.join
      ¬(List.zip diffs repeatedShortPattern |>.all (fun (a, b) => a = b))
  := sorry

theorem arithmetic_sequence_pattern (d : Int) (len : Nat) (h₁ : 1 ≤ d ∧ d ≤ 9) (h₂ : 2 ≤ len ∧ len ≤ 100) :
  let arithmetic := List.range len |>.map (fun n => Int.ofNat n * d)
  match findPattern arithmetic with
  | none => False
  | some pattern =>
    pattern.length = 1 ∧ pattern.head! = d
  := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_pattern [1, 2, 3, 4, 5]

/-
info: [1, 1, 1, 1, -1, -1, -1, -1]
-/
-- #guard_msgs in
-- #eval find_pattern [1, 2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5, 4, 3, 2, 1]

/-
info: [1, 2, -1, -2, -2, 1, 2, -1, -2]
-/
-- #guard_msgs in
-- #eval find_pattern [4, 5, 7, 6, 4, 2, 3, 5, 4, 2, 3, 5, 4, 2, 0, 1, 3, 2, 0, 1, 3, 2, 0, -2, -1, 1, 0, -2]

-- Apps difficulty: introductory
-- Assurance level: guarded