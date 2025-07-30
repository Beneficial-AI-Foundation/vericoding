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
  · simp [split]
    induction l with
    | nil => simp
    | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys =>
        simp
        cases ys with
        | nil => simp; omega
        | cons z zs =>
          simp
          omega
  · simp [split]
    induction l with
    | nil => simp
    | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys =>
        simp
        cases ys with
        | nil => simp; omega
        | cons z zs =>
          simp
          omega
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
  | case3 x xs y ys ih =>
    simp [merge, is_sorted_asc]
    by_cases h : x <= y
    · simp [h]
      cases xs with
      | nil => simp [is_sorted_asc_helper]
      | cons x' xs' =>
        simp [is_sorted_asc_helper]
        by_cases h' : x <= x'
        · simp [h']
          apply ih
          · simp [is_sorted_asc] at h1
            simp [is_sorted_asc_helper] at h1
            simp [h'] at h1
            exact h1
          · exact h2
        · simp [h']
    · simp [h]
      cases ys with
      | nil => simp [is_sorted_asc_helper]
      | cons y' ys' =>
        simp [is_sorted_asc_helper]
        by_cases h' : y <= y'
        · simp [h']
          apply ih
          · exact h1
          · simp [is_sorted_asc] at h2
            simp [is_sorted_asc_helper] at h2
            simp [h'] at h2
            exact h2
        · simp [h']

-- LLM HELPER
lemma merge_sort_sorted (l : List Int) : is_sorted_asc (merge_sort l) = true := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case2 => simp [merge_sort, is_sorted_asc, is_sorted_asc_helper]
  | case3 a ih1 ih2 =>
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
  | case3 x xs y ys ih =>
    simp [merge]
    by_cases h : x <= y
    · simp [h]
      rw [List.count_cons, ih]
      by_cases h' : x = n
      · simp [h']; ring
      · simp [h']; ring
    · simp [h]
      rw [List.count_cons, ih]
      by_cases h' : y = n
      · simp [h']; ring
      · simp [h']; ring

-- LLM HELPER
lemma split_count (l : List Int) (n : Int) : 
  l.count n = (split l).1.count n + (split l).2.count n := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 => simp [split]
  | case3 x y rest ih =>
    simp [split]
    rw [List.count_cons, List.count_cons, ih]
    ring

-- LLM HELPER
lemma merge_sort_count (l : List Int) : ∀ n, l.count n = (merge_sort l).count n := by
  induction l using merge_sort.induct with
  | case1 => simp [merge_sort]
  | case2 => simp [merge_sort]
  | case3 a ih1 ih2 =>
    simp [merge_sort]
    intro n
    rw [merge_count]
    rw [← ih1, ← ih2]
    exact split_count a n

-- LLM HELPER
lemma number_to_word_map_inv (n : Int) : 
  0 ≤ n → n ≤ 9 → word_to_number_map (number_to_word_map n) = n := by
  intro h1 h2
  interval_cases n <;> simp [number_to_word_map, word_to_number_map]

-- LLM HELPER
lemma word_to_number_map_bounds (s : String) : 
  word_to_number_map s ≠ -1 → 0 ≤ word_to_number_map s ∧ word_to_number_map s ≤ 9 := by
  intro h
  simp [word_to_number_map] at h ⊢
  cases s <;> simp at h <;> omega

theorem correctness
(numbers: String)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h_valid
    simp [implementation]
    constructor
    · simp [List.length_map]
    · constructor
      · intro n h_in
        use n
        simp [List.mem_map, List.map_map] at h_in ⊢
        obtain ⟨s, hs1, hs2⟩ := h_in
        rw [← hs2]
        use number_to_word_map (word_to_number_map s)
        constructor
        · simp [List.mem_map]
          use word_to_number_map s
          constructor
          · have : word_to_number_map s ∈ numbers.splitOn " ".map word_to_number_map := by
              simp [List.mem_map]
              use s
              exact ⟨hs1, rfl⟩
            have perm := merge_sort_count (numbers.splitOn " ".map word_to_number_map) (word_to_number_map s)
            simp [List.mem_iff_count_pos] at this ⊢
            rw [← perm] at this
            exact this
          · have h_ne : word_to_number_map s ≠ -1 := by
              intro h_neg
              rw [h_neg] at hs2
              rw [← hs2] at h_valid
              simp at h_valid
              exact h_valid ⟨s, hs1, h_neg⟩
            have bounds := word_to_number_map_bounds s h_ne
            exact number_to_word_map_inv (word_to_number_map s) bounds.1 bounds.2
        · rw [← hs2]
          have h_ne : word_to_number_map s ≠ -1 := by
            intro h_neg
            rw [h_neg] at hs2
            rw [← hs2] at h_valid
            simp at h_valid
            exact h_valid ⟨s, hs1, h_neg⟩
          have bounds := word_to_number_map_bounds s h_ne
          exact number_to_word_map_inv (word_to_number_map s) bounds.1 bounds.2
      · constructor
        · intro n h_in
          use n
          simp [List.mem_map, List.map_map] at h_in ⊢
          obtain ⟨s, hs1, hs2⟩ := h_in
          simp [List.mem_map] at hs1
          obtain ⟨num, hnum1, hnum2⟩ := hs1
          rw [← hnum2, ← hs2]
          have : num ∈ numbers.splitOn " ".map word_to_number_map := by
            have perm := merge_sort_count (numbers.splitOn " ".map word_to_number_map) num
            simp [List.mem_iff_count_pos] at hnum1 ⊢
            rw [← perm] at hnum1
            exact hnum1
          simp [List.mem_map] at this
          obtain ⟨orig_s, horig1, horig2⟩ := this
          rw [← horig2]
          use orig_s
          constructor
          · exact horig1
          · have h_ne : word_to_number_map orig_s ≠ -1 := by
              intro h_neg
              rw [h_neg] at horig2
              rw [← horig2] at h_valid
              simp at h_valid
              exact h_valid ⟨orig_s, horig1, h_neg⟩
            have bounds := word_to_number_map_bounds orig_s h_ne
            exact number_to_word_map_inv (word_to_number_map orig_s) bounds.1 bounds.2
        · constructor
          · intro n
            simp [List.map_map]
            have : (merge_sort (numbers.splitOn " ".map word_to_number_map)).map (fun x => word_to_number_map (number_to_word_map x)) = merge_sort (numbers.splitOn " ".map word_to_number_map) := by
              congr 1
              ext x
              by_cases h : x ∈ merge_sort (numbers.splitOn " ".map word_to_number_map)
              · have : x ∈ numbers.splitOn " ".map word_to_number_map := by
                  have perm := merge_sort_count (numbers.splitOn " ".map word_to_number_map) x
                  simp [List.mem_iff_count_pos] at h ⊢
                  rw [← perm] at h
                  exact h
                simp [List.mem_map] at this
                obtain ⟨s, hs1, hs2⟩ := this
                rw [← hs2]
                have h_ne : word_to_number_map s ≠ -1 := by
                  intro h_neg
                  rw [h_neg] at hs2
                  rw [← hs2] at h_valid
                  simp at h_valid
                  exact h_valid ⟨s, hs1, h_neg⟩
                have bounds := word_to_number_map_bounds s h_ne
                exact number_to_word_map_inv (word_to_number_map s) bounds.1 bounds.2
              · simp [number_to_word_map]
                split <;> simp [word_to_number_map]
            rw [this]
            exact merge_sort_count (numbers.splitOn " ".map word_to_number_map) n
          · simp [List.map_map]
            have : (merge_sort (numbers.splitOn " ".map word_to_number_map)).map (fun x => word_to_number_map (number_to_word_map x)) = merge_sort (numbers.splitOn " ".map word_to_number_map) := by
              congr 1
              ext x
              by_cases h : x ∈ merge_sort (numbers.splitOn " ".map word_to_number_map)
              · have : x ∈ numbers.splitOn " ".map word_to_number_map := by
                  have perm := merge_sort_count (numbers.splitOn " ".map word_to_number_map) x
                  simp [List.mem_iff_count_pos] at h ⊢
                  rw [← perm] at h
                  exact h
                simp [List.mem_map] at this
                obtain ⟨s, hs1, hs2⟩ := this
                rw [← hs2]
                have h_ne : word_to_number_map s ≠ -1 := by
                  intro h_neg
                  rw [h_neg] at hs2
                  rw [← hs2] at h_valid
                  simp at h_valid
                  exact h_valid ⟨s, hs1, h_neg⟩
                have bounds := word_to_number_map_bounds s h_ne
                exact number_to_word_map_inv (word_to_number_map s) bounds.1 bounds.2
              · simp [number_to_word_map]
                split <;> simp [word_to_number_map]
            rw [this]
            exact merge_sort_sorted (numbers.splitOn " ".map word_to_number_map)