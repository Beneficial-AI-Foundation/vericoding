import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

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
  | [x] => is_sorted
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
def number_to_word_map : Int → String := fun n =>
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

-- LLM HELPER
def sort_list : List Int → List Int := fun l =>
  l.mergeSort (fun x y => x <= y)

def implementation (numbers: String) : String :=
  let numbers_split := numbers.splitOn " "
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
  let numbers_as_ints := numbers_split.map word_to_number_map
  let sorted_numbers := sort_list numbers_as_ints
  let sorted_words := sorted_numbers.map number_to_word_map
  " ".intercalate sorted_words

theorem correctness
(numbers: String)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
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
  let is_sorted_asc : List Int → Bool := fun numbers =>
    let rec is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
      match numbers with
      | [] => is_sorted
      | [x] => is_sorted
      | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false
    is_sorted_asc_helper numbers false
  let numbers_split := numbers.splitOn " "
  let numbers_as_ints := numbers_split.map word_to_number_map
  let sorted_numbers := sort_list numbers_as_ints
  let sorted_words := sorted_numbers.map number_to_word_map
  let result := " ".intercalate sorted_words
  let result_split := result.splitOn " "
  let result_mapped_to_numbers := result_split.map word_to_number_map
  let numbers_as_str_mapped_to_numbers := numbers_split.map word_to_number_map
  use result
  constructor
  · rfl
  · intro h
    constructor
    · sorry
    constructor
    · sorry
    constructor
    · sorry
    constructor
    · sorry
    · sorry