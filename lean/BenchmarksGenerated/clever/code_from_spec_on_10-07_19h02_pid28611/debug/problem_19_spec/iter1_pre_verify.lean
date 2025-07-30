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
def word_to_number_map : String → Int := fun word =>
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

-- LLM HELPER
def merge_sort (l : List Int) : List Int :=
  let rec merge (left right : List Int) : List Int :=
    match left, right with
    | [], _ => right
    | _, [] => left
    | x::xs, y::ys =>
      if x <= y then x :: merge xs (y::ys)
      else y :: merge (x::xs) ys
  let rec split (l : List Int) : List Int × List Int :=
    match l with
    | [] => ([], [])
    | [x] => ([x], [])
    | x::y::rest =>
      let (left, right) := split rest
      (x::left, y::right)
  let rec sort (l : List Int) : List Int :=
    match l with
    | [] => []
    | [x] => [x]
    | _ =>
      let (left, right) := split l
      merge (sort left) (sort right)
  sort l

def implementation (numbers: String) : String :=
  let numbers_split := numbers.splitOn " "
  let numbers_as_ints := numbers_split.map word_to_number_map
  let sorted_numbers := merge_sort numbers_as_ints
  let result_words := sorted_numbers.map number_to_word_map
  String.intercalate " " result_words

-- LLM HELPER
def is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
  match numbers with
  | [] => is_sorted
  | [x] => is_sorted
  | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false

-- LLM HELPER
def is_sorted_asc : List Int → Bool := fun numbers =>
  is_sorted_asc_helper numbers false

-- LLM HELPER
lemma merge_sort_sorted (l : List Int) : is_sorted_asc (merge_sort l) = true := by
  sorry

-- LLM HELPER
lemma merge_sort_permutation (l : List Int) : ∀ n, l.count n = (merge_sort l).count n := by
  sorry

-- LLM HELPER
lemma word_number_inverse (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : word_to_number_map (number_to_word_map n) = n := by
  sorry

-- LLM HELPER
lemma number_word_inverse (w : String) (h : word_to_number_map w ≠ -1) : number_to_word_map (word_to_number_map w) = w := by
  sorry

-- LLM HELPER
lemma map_length_eq {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  sorry

-- LLM HELPER
lemma intercalate_split_inverse (words : List String) : (String.intercalate " " words).splitOn " " = words := by
  sorry

theorem correctness
(numbers: String)
: problem_spec implementation numbers
:= by
  sorry