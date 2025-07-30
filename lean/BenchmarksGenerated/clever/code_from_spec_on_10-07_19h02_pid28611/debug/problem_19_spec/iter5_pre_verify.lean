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
def merge (left right : List Int) : List Int :=
  match left, right with
  | [], _ => right
  | _, [] => left
  | x::xs, y::ys =>
    if x <= y then x :: merge xs (y::ys)
    else y :: merge (x::xs) ys

-- LLM HELPER
def split (l : List Int) : List Int × List Int :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x::y::rest =>
    let (left, right) := split rest
    (x::left, y::right)

-- LLM HELPER
def merge_sort (l : List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    let (left, right) := split l
    merge (merge_sort left) (merge_sort right)
termination_by l.length
decreasing_by {
  simp_wf
  constructor
  · have h : (split l).1.length < l.length := by
      cases l with
      | nil => simp [split]
      | cons x t =>
        cases t with
        | nil => simp [split]
        | cons y rest =>
          simp [split]
          omega
    exact h
  · have h : (split l).2.length < l.length := by
      cases l with
      | nil => simp [split]
      | cons x t =>
        cases t with
        | nil => simp [split]
        | cons y rest =>
          simp [split]
          omega
    exact h
}

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
  | [_] => is_sorted
  | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false

-- LLM HELPER
def is_sorted_asc : List Int → Bool := fun numbers =>
  is_sorted_asc_helper numbers false

-- LLM HELPER
lemma merge_sorted (l1 l2 : List Int) : 
  is_sorted_asc l1 = true → is_sorted_asc l2 = true → is_sorted_asc (merge l1 l2) = true := by
  intro h1 h2
  induction l1, l2 using merge.induct with
  | case1 => simp [merge, h2]
  | case2 => simp [merge, h1]
  | case3 x xs y ys ih1 ih2 =>
    simp [merge]
    by_cases h : x <= y
    · simp [h]
      rw [is_sorted_asc, is_sorted_asc_helper]
      simp [is_sorted_asc_helper]
      sorry
    · simp [h]
      rw [is_sorted_asc, is_sorted_asc_helper]
      simp [is_sorted_asc_helper]
      sorry

-- LLM HELPER
lemma merge_sort_sorted (l : List Int) : is_sorted_asc (merge_sort l) = true := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case2 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case3 a b rest ih1 ih2 =>
    simp [merge_sort]
    apply merge_sorted
    · exact ih1
    · exact ih2

-- LLM HELPER
lemma merge_count (l1 l2 : List Int) (n : Int) : 
  (merge l1 l2).count n = l1.count n + l2.count n := by
  induction l1, l2 using merge.induct with
  | case1 => simp [merge]
  | case2 => simp [merge]
  | case3 x xs y ys ih1 ih2 =>
    simp [merge]
    by_cases h : x <= y
    · simp [h]
      rw [List.count_cons, ih1]
      by_cases h' : x = n
      · simp [h']
        ring
      · simp [h']
        ring
    · simp [h]
      rw [List.count_cons, ih2]
      by_cases h' : y = n
      · simp [h']
        ring
      · simp [h']
        ring

-- LLM HELPER
lemma merge_sort_permutation (l : List Int) : ∀ n, l.count n = (merge_sort l).count n := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort]
  | case2 => simp [merge_sort]
  | case3 a b rest ih1 ih2 =>
    simp [merge_sort]
    intro n
    rw [merge_count]
    have h_split : ∀ n, (a::b::rest).count n = (split (a::b::rest)).1.count n + (split (a::b::rest)).2.count n := by
      intro n
      simp [split]
      ring
    rw [← ih1, ← ih2]
    exact h_split n

-- LLM HELPER
lemma split_intercalate (words : List String) : 
  words ≠ [] → (String.intercalate " " words).splitOn " " = words := by
  intro h_ne_empty
  induction words with
  | nil => contradiction
  | cons h t ih =>
    cases' t with
    | nil => simp [String.intercalate, String.splitOn]
    | cons h' t' => 
      simp [String.intercalate]
      have : (String.intercalate " " (h' :: t')).splitOn " " = h' :: t' := by
        apply ih
        simp
      simp [String.splitOn]
      exact this

theorem correctness
(numbers: String)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use (let numbers_split := numbers.splitOn " ";
       let numbers_as_ints := numbers_split.map word_to_number_map;
       let sorted_numbers := merge_sort numbers_as_ints;
       let result_words := sorted_numbers.map number_to_word_map;
       String.intercalate " " result_words)
  constructor
  · rfl
  · intro h_valid
    simp [word_to_number_map, is_sorted_asc, is_sorted_asc_helper]
    constructor
    · simp [List.length_map]
    · constructor
      · intro n h_in_orig
        use n
        have : n ∈ (numbers.splitOn " ").map word_to_number_map := h_in_orig
        have perm := merge_sort_permutation ((numbers.splitOn " ").map word_to_number_map) n
        rw [← perm] at this
        exact this
      · constructor
        · intro n h_in_result
          use n
          have perm := merge_sort_permutation ((numbers.splitOn " ").map word_to_number_map) n
          rw [perm] at h_in_result
          exact h_in_result
        · constructor
          · intro n
            exact merge_sort_permutation ((numbers.splitOn " ").map word_to_number_map) n
          · exact merge_sort_sorted ((numbers.splitOn " ").map word_to_number_map)