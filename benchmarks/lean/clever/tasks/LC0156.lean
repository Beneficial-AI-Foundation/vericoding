-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (words: List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List String → String)
-- inputs
(words: List String) :=
let unique_chars (string: String) :=
  let string_idx := {i: Nat | i < string.length}.toFinset;
  let characters := string_idx.image (fun i => string.toList[i]!);
  characters.card;
-- spec
let spec (result: String) :=
(result = "" ↔ words.length = 0) ∧
(words.length != 0 → result ∈ words ∧
let unique_chars_list := words.map unique_chars;
let max_unique_chars := unique_chars_list.max?.get!;
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]! = max_unique_chars →
  result ≤ words[i]!);
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

theorem correctness
(words: List String)
: problem_spec implementation words := by
  sorry
-- </vc-theorems>