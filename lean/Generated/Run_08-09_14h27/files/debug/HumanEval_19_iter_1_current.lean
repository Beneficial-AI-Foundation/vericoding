/- 
function_signature: "def sort_numbers(numbers: str) -> str"
docstring: |
    Input is a space-delimited string of numberals from 'zero' to 'nine'.
    Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
    Return the string with numbers sorted from smallest to largest
test_cases:
  - input: "three one five"
    expected_output: "one three five"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def number_to_word (n: Int) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | 9 => "nine"
  | _ => ""

def implementation (numbers: String) : String :=
  let word_to_number_map : String → Int := fun word =>
    match word with
    | "zero" => 0
    | "one" => 1
    | "two" => 2
    | "three" => 3
    | "four" => 4
    | "five" => 5
    | "six" => 6
    | "seven" => 7
    | "eight" => 8
    | "nine" => 9
    | _ => -1
  let words := numbers.splitOn " "
  let numbers_as_ints := words.map word_to_number_map
  let sorted_numbers := numbers_as_ints.mergeSort (· ≤ ·)
  let sorted_words := sorted_numbers.map number_to_word
  String.intercalate " " sorted_words

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(numbers: String) :=
-- spec
let word_to_number_map : String → Int := fun word =>
  match word with
  | "zero" => 0
  | "one" => 1
  | "two" => 2
  | "three" => 3
  | "four" => 4
  | "five" => 5
  | "six" => 6
  | "seven" => 7
  | "eight" => 8
  | "nine" => 9
  | _ => -1;
let is_sorted_asc : List Int → Bool := fun numbers =>
let rec is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
  match numbers with
  | [] => is_sorted
  | [_] => is_sorted
  | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false;
is_sorted_asc_helper numbers false;
let spec (result: String) :=
let result_split := result.splitOn " ";
let numbers_split := numbers.splitOn " ";
let result_mapped_to_numbers := result_split.map word_to_number_map;
let numbers_as_str_mapped_to_numbers := numbers_split.map word_to_number_map;
¬ -1 ∈ numbers_as_str_mapped_to_numbers →
result_split.length = numbers_split.length ∧
(∀ n, n ∈ numbers_as_str_mapped_to_numbers →
∃ m, m ∈ result_mapped_to_numbers) ∧
(∀ n, n ∈ result_mapped_to_numbers →
∃ m, m ∈ numbers_as_str_mapped_to_numbers) ∧
(∀ n, numbers_as_str_mapped_to_numbers.count n = result_mapped_to_numbers.count n) ∧
is_sorted_asc result_mapped_to_numbers = true;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma word_to_number_number_to_word_inverse (n : Int) (h : 0 ≤ n ∧ n ≤ 9) :
  let word_to_number_map : String → Int := fun word =>
    match word with
    | "zero" => 0
    | "one" => 1
    | "two" => 2
    | "three" => 3
    | "four" => 4
    | "five" => 5
    | "six" => 6
    | "seven" => 7
    | "eight" => 8
    | "nine" => 9
    | _ => -1
  word_to_number_map (number_to_word n) = n := by
  simp [number_to_word]
  interval_cases n <;> simp

-- LLM HELPER
lemma is_sorted_asc_correct (l : List Int) :
  let is_sorted_asc : List Int → Bool := fun numbers =>
    let rec is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
      match numbers with
      | [] => is_sorted
      | [_] => is_sorted
      | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false;
    is_sorted_asc_helper numbers false;
  is_sorted_asc l = true ↔ List.Sorted (· ≤ ·) l := by
  sorry

theorem correctness
(numbers: String)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use (String.intercalate " " ((numbers.splitOn " ").map (fun word =>
    match word with
    | "zero" => 0
    | "one" => 1
    | "two" => 2
    | "three" => 3
    | "four" => 4
    | "five" => 5
    | "six" => 6
    | "seven" => 7
    | "eight" => 8
    | "nine" => 9
    | _ => -1)).mergeSort (· ≤ ·)).map number_to_word)
  constructor
  · simp [String.intercalate]
  · intro h
    constructor
    · simp [String.splitOn, List.map, List.mergeSort]
      sorry
    constructor
    · intro n hn
      simp at hn ⊢
      sorry
    constructor
    · intro n hn
      simp at hn ⊢
      sorry
    constructor
    · intro n
      simp
      sorry
    · simp
      rw [is_sorted_asc_correct]
      exact List.sorted_mergeSort (· ≤ ·) _

-- #test implementation "three one five" = "one three five"