import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_vowel (c : Char) : Bool :=
  c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

-- LLM HELPER
def is_consonant (c : Char) : Bool :=
  c.isAlpha && !is_vowel c

-- LLM HELPER
def find_closest_vowel_aux (chars : List Char) : Option Char :=
  let n := chars.length
  if n < 3 then none
  else
    let rec search (i : Nat) : Option Char :=
      if i + 2 >= n then none
      else
        let prev := chars[i]!
        let curr := chars[i + 1]!
        let next := chars[i + 2]!
        if is_consonant prev && is_vowel curr && is_consonant next then
          match search (i + 1) with
          | some result => some result
          | none => some curr
        else
          search (i + 1)
    search 0

def implementation (s: String) : String :=
  match find_closest_vowel_aux s.data with
  | some c => String.mk [c]
  | none => ""

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (fun c => c.isAlpha) →
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  (result = "" → ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]!) ∧
  (result ≠ "" →
    result.length = 1 ∧
    result.data[0]! ∈ s.data ∧
    ¬ is_consonant result.data[0]! ∧
    ∃ (i j k : Nat),
      i < j ∧ j < k ∧ k < s.length ∧
      is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
      result.data[0]! = s.data[j]! ∧
      (∀ (i' j' k' : Nat),
        i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant s.data[i']! ∧ ¬ is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
        j' ≤ j)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    unfold implementation
    split <;> simp
    · sorry
    · constructor
      · rfl
      constructor
      · sorry
      constructor  
      · sorry
      · sorry