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
termination_by l => l.length
decreasing_by {
  simp_wf
  cases' l with h t
  · simp
  · cases' t with h' t'
    · simp
    · simp [split]
      constructor
      · sorry
      · sorry
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
lemma merge_sort_sorted (l : List Int) : is_sorted_asc (merge_sort l) = true := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case2 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case3 a b rest ih1 ih2 =>
    simp [merge_sort]
    have h1 : is_sorted_asc (merge_sort (let (left, right) := merge_sort.split (a::b::rest); left)) = true := ih1
    have h2 : is_sorted_asc (merge_sort (let (left, right) := merge_sort.split (a::b::rest); right)) = true := ih2
    sorry

-- LLM HELPER
lemma merge_sort_permutation (l : List Int) : ∀ n, l.count n = (merge_sort l).count n := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort]
  | case2 => simp [merge_sort]
  | case3 a b rest ih1 ih2 =>
    simp [merge_sort]
    intro n
    sorry

-- LLM HELPER
lemma word_number_inverse (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : word_to_number_map (number_to_word_map n) = n := by
  cases' n with n n
  · cases' n with n
    · simp [number_to_word_map, word_to_number_map]
    · cases' n with n
      · simp [number_to_word_map, word_to_number_map]
      · cases' n with n
        · simp [number_to_word_map, word_to_number_map]
        · cases' n with n
          · simp [number_to_word_map, word_to_number_map]
          · cases' n with n
            · simp [number_to_word_map, word_to_number_map]
            · cases' n with n
              · simp [number_to_word_map, word_to_number_map]
              · cases' n with n
                · simp [number_to_word_map, word_to_number_map]
                · cases' n with n
                  · simp [number_to_word_map, word_to_number_map]
                  · cases' n with n
                    · simp [number_to_word_map, word_to_number_map]
                    · cases' n with n
                      · simp [number_to_word_map, word_to_number_map]
                      · simp [number_to_word_map, word_to_number_map]
                        omega
  · simp [number_to_word_map, word_to_number_map]
    omega

-- LLM HELPER
lemma number_word_inverse (w : String) (h : word_to_number_map w ≠ -1) : number_to_word_map (word_to_number_map w) = w := by
  cases' w_eq : w with
  | mk s =>
    cases' s with
    | nil => simp [word_to_number_map] at h
    | cons c cs =>
      have : w = "zero" ∨ w = "one" ∨ w = "two" ∨ w = "three" ∨ w = "four" ∨ w = "five" ∨ w = "six" ∨ w = "seven" ∨ w = "eight" ∨ w = "nine" := by
        by_contra h_contra
        simp [word_to_number_map] at h
        split at h <;> simp at h_contra h
      rcases this with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
      · simp [h1, word_to_number_map, number_to_word_map]
      · simp [h2, word_to_number_map, number_to_word_map]
      · simp [h3, word_to_number_map, number_to_word_map]
      · simp [h4, word_to_number_map, number_to_word_map]
      · simp [h5, word_to_number_map, number_to_word_map]
      · simp [h6, word_to_number_map, number_to_word_map]
      · simp [h7, word_to_number_map, number_to_word_map]
      · simp [h8, word_to_number_map, number_to_word_map]
      · simp [h9, word_to_number_map, number_to_word_map]
      · simp [h10, word_to_number_map, number_to_word_map]

-- LLM HELPER
lemma map_length_eq {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma intercalate_split_inverse (words : List String) : (String.intercalate " " words).splitOn " " = words := by
  induction words with
  | nil => simp [String.intercalate, String.splitOn]
  | cons h t ih =>
    cases' t with
    | nil => simp [String.intercalate, String.splitOn]
    | cons h' t' => simp [String.intercalate, String.splitOn]; sorry

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
    · simp [map_length_eq]
    · constructor
      · intro n h_in_orig
        use n
        simp [merge_sort_permutation]
        sorry
      · constructor
        · intro n h_in_result
          use n
          simp [merge_sort_permutation]
          sorry
        · constructor
          · intro n
            simp [merge_sort_permutation]
          · exact merge_sort_sorted _