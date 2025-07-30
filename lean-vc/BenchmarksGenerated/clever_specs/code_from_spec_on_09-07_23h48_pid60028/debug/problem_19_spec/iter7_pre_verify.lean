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
def number_to_word : Int → String := fun n =>
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
def quicksort (l : List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | h :: t =>
    let smaller := (t.attach.filter (fun x => x.val <= h)).unattach
    let bigger := (t.attach.filter (fun x => x.val > h)).unattach
    quicksort smaller ++ [h] ++ quicksort bigger
  termination_by l.length
  decreasing_by
    simp_wf
    · apply List.length_filter_unattach_lt
      simp
    · apply List.length_filter_unattach_lt
      simp

-- LLM HELPER
lemma List.length_filter_unattach_lt {α : Type*} {l : List α} {p : α → Bool} (hl : l ≠ []) : 
  (l.attach.filter (fun x => p x.val)).unattach.length < l.length := by
  have : (l.attach.filter (fun x => p x.val)).unattach.length ≤ l.attach.unattach.length := by
    simp [List.length_unattach]
    apply List.length_filter_le
  simp [List.length_unattach] at this
  cases' l with h t
  · contradiction
  · simp at this
    by_cases h_ex : ∃ x ∈ (h :: t).attach, p x.val
    · have : (h :: t).attach.filter (fun x => p x.val) ≠ [] := by
        simp [List.filter_eq_nil_iff]
        exact h_ex
      have len_pos : ((h :: t).attach.filter (fun x => p x.val)).length > 0 := by
        simp [List.length_pos_iff_ne_nil]
        exact this
      have : ((h :: t).attach.filter (fun x => p x.val)).unattach.length < (h :: t).length := by
        simp [List.length_unattach]
        apply Nat.lt_succ_iff.mpr
        exact List.length_filter_le _ _
      exact this
    · have : (h :: t).attach.filter (fun x => p x.val) = [] := by
        simp [List.filter_eq_nil_iff]
        exact h_ex
      simp [this, List.length_unattach]

def implementation (numbers: String) : String :=
  let words := numbers.splitOn " "
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
  let number_list := words.map word_to_number_map
  let sorted_numbers := quicksort number_list
  let result_words := sorted_numbers.map number_to_word
  String.intercalate " " result_words

-- LLM HELPER
lemma word_to_number_inverse (n : Int) (h : 0 ≤ n ∧ n ≤ 9) : 
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
  cases' h with h1 h2
  interval_cases n <;> simp

-- LLM HELPER  
lemma quicksort_sorted (l : List Int) : 
  let is_sorted_asc : List Int → Bool := fun numbers =>
    let rec is_sorted_asc_helper : List Int → Bool → Bool := fun numbers is_sorted =>
      match numbers with
      | [] => is_sorted
      | [_] => is_sorted
      | x::y::rest => if x <= y then is_sorted_asc_helper (y::rest) true else false;
    is_sorted_asc_helper numbers false;
  is_sorted_asc (quicksort l) = true := by
  sorry

-- LLM HELPER
lemma quicksort_permutation (l : List Int) : 
  ∀ x, l.count x = (quicksort l).count x := by
  sorry

theorem correctness
(numbers: String)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp
  use String.intercalate " " ((quicksort (numbers.splitOn " ").map (fun word => match word with | "zero" => 0 | "one" => 1 | "two" => 2 | "three" => 3 | "four" => 4 | "five" => 5 | "six" => 6 | "seven" => 7 | "eight" => 8 | "nine" => 9 | _ => -1)).map number_to_word)
  constructor
  · rfl
  · intro h
    constructor
    · simp only [String.splitOn_intercalate]
      rw [List.length_map, List.length_map]
    constructor
    · intro n hn
      simp [List.map_map]
      use n
      rw [← quicksort_permutation]
      exact hn
    constructor
    · intro n hn
      simp [List.map_map]  
      use n
      rw [quicksort_permutation]
      exact hn
    constructor
    · intro n
      simp [List.map_map]
      rw [quicksort_permutation]
    · apply quicksort_sorted