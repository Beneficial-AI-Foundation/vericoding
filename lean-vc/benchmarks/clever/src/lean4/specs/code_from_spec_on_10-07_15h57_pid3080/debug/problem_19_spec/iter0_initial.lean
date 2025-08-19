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
def merge_sort (xs : List Int) : List Int :=
  let rec merge : List Int → List Int → List Int
    | [], ys => ys
    | xs, [] => xs
    | x::xs, y::ys => if x <= y then x :: merge xs (y::ys) else y :: merge (x::xs) ys
  let rec split : List Int → List Int × List Int
    | [] => ([], [])
    | [x] => ([x], [])
    | x::y::xs => let (left, right) := split xs; (x::left, y::right)
  let rec sort : List Int → List Int
    | [] => []
    | [x] => [x]
    | xs => let (left, right) := split xs; merge (sort left) (sort right)
  sort xs

def implementation (numbers: String) : String := 
  let words := numbers.splitOn " "
  let numbers_list := words.map word_to_number_map
  let sorted_numbers := merge_sort numbers_list
  let sorted_words := sorted_numbers.map number_to_word_map
  String.intercalate " " sorted_words

-- LLM HELPER
lemma word_to_number_map_inverse (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : 
  word_to_number_map (number_to_word_map n) = n := by
  rcases h with ⟨h1, h2⟩
  interval_cases n <;> rfl

-- LLM HELPER
lemma number_to_word_map_inverse (s : String) (h : word_to_number_map s ≠ -1) : 
  number_to_word_map (word_to_number_map s) = s := by
  unfold word_to_number_map number_to_word_map at *
  by_cases h1 : s = "zero"
  · simp [h1]
  by_cases h2 : s = "one"
  · simp [h2]
  by_cases h3 : s = "two"
  · simp [h3]
  by_cases h4 : s = "three"
  · simp [h4]
  by_cases h5 : s = "four"
  · simp [h5]
  by_cases h6 : s = "five"
  · simp [h6]
  by_cases h7 : s = "six"
  · simp [h7]
  by_cases h8 : s = "seven"
  · simp [h8]
  by_cases h9 : s = "eight"
  · simp [h9]
  by_cases h10 : s = "nine"
  · simp [h10]
  · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at h
    contradiction

-- LLM HELPER
lemma merge_sort_sorted (xs : List Int) : 
  let sorted := merge_sort xs
  ∀ i j, i < j → j < sorted.length → sorted.get ⟨i, by omega⟩ ≤ sorted.get ⟨j, by omega⟩ := by
  sorry

-- LLM HELPER
lemma merge_sort_perm (xs : List Int) : xs.toFinset = (merge_sort xs).toFinset := by
  sorry

-- LLM HELPER
lemma merge_sort_count (xs : List Int) (x : Int) : xs.count x = (merge_sort xs).count x := by
  sorry

-- LLM HELPER
lemma is_sorted_asc_merge_sort (xs : List Int) : 
  let is_sorted_asc : List Int → Bool := fun numbers =>
    let rec is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
      match numbers with
      | [] => is_sorted
      | [x] => is_sorted
      | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false;
    is_sorted_asc_helper numbers false
  is_sorted_asc (merge_sort xs) = true := by
  sorry

theorem correctness
(numbers: String)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp
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
      | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false;
    is_sorted_asc_helper numbers false
  let words := numbers.splitOn " "
  let numbers_list := words.map word_to_number_map
  let sorted_numbers := merge_sort numbers_list
  let sorted_words := sorted_numbers.map number_to_word_map
  let result := String.intercalate " " sorted_words
  use result
  constructor
  · rfl
  · intro h
    constructor
    · simp [result]
      sorry
    constructor
    · sorry
    constructor
    · sorry
    constructor
    · sorry
    · sorry