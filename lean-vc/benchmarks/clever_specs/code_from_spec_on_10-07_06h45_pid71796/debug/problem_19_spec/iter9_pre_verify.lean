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
def insertSort : List Int → List Int
  | [] => []
  | x :: xs => insert x (insertSort xs)
where insert : Int → List Int → List Int
  | x, [] => [x]
  | x, y :: ys => if x <= y then x :: y :: ys else y :: insert x ys

-- LLM HELPER
def isSorted : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x <= y && isSorted (y :: rest)

-- LLM HELPER
lemma insertSort_sorted : ∀ l : List Int, isSorted (insertSort l) = true := by
  intro l
  induction l with
  | nil => simp [insertSort, isSorted]
  | cons x xs ih => 
    simp [insertSort]
    have h : isSorted (insertSort.insert x (insertSort xs)) = true := by
      apply insert_maintains_sorted
      exact ih
    exact h
where insert_maintains_sorted : ∀ x : Int, ∀ l : List Int, isSorted l = true → isSorted (insertSort.insert x l) = true := by
  intro x l h
  induction l with
  | nil => simp [insertSort.insert, isSorted]
  | cons y ys ih =>
    simp [insertSort.insert]
    split_ifs with h_le
    · simp [isSorted]
      exact h
    · simp [isSorted]
      cases' ys with z zs
      · simp [isSorted, insertSort.insert]
      · simp [isSorted] at h
        cases' h with h1 h2
        simp [isSorted, insertSort.insert]
        split_ifs with h_le2
        · constructor
          · exact le_of_not_gt (fun h_gt => h_le (le_of_lt h_gt))
          · exact h2
        · exact ih h2

-- LLM HELPER
lemma is_sorted_asc_equiv : ∀ l : List Int, problem_spec.is_sorted_asc l = isSorted l := by
  intro l
  simp [problem_spec.is_sorted_asc]
  induction l with
  | nil => simp [problem_spec.is_sorted_asc_helper, isSorted]
  | cons x xs ih =>
    cases' xs with y ys
    · simp [problem_spec.is_sorted_asc_helper, isSorted]
    · simp [problem_spec.is_sorted_asc_helper, isSorted]
      split_ifs with h_le
      · simp [ih]
      · simp

-- LLM HELPER
lemma splitOn_intercalate_length : ∀ (words : List String), 
  ((" ".intercalate words).splitOn " ").length = words.length := by
  intro words
  induction words with
  | nil => simp [String.intercalate, String.splitOn]
  | cons w ws ih =>
    simp [String.intercalate]
    cases' ws with w' ws'
    · simp [String.splitOn]
    · simp [String.splitOn, String.intercalate]
      exact ih

-- LLM HELPER
lemma splitOn_intercalate_mem : ∀ (words : List String) (w : String),
  w ∈ words → w ∈ ((" ".intercalate words).splitOn " ") := by
  intro words w h
  induction words with
  | nil => simp at h
  | cons w' ws ih =>
    simp at h
    cases' h with h1 h2
    · simp [String.intercalate, String.splitOn]
      left
      exact h1
    · simp [String.intercalate, String.splitOn]
      right
      exact ih h2

-- LLM HELPER
lemma mem_splitOn_intercalate : ∀ (words : List String) (w : String),
  w ∈ ((" ".intercalate words).splitOn " ") → w ∈ words := by
  intro words w h
  induction words with
  | nil => simp [String.intercalate, String.splitOn] at h
  | cons w' ws ih =>
    simp [String.intercalate, String.splitOn] at h
    cases' h with h1 h2
    · left
      exact h1
    · right
      exact ih h2

-- LLM HELPER
lemma count_map_insertSort : ∀ (l : List Int) (n : Int),
  l.count n = (insertSort l).count n := by
  intro l n
  induction l with
  | nil => simp [insertSort]
  | cons x xs ih =>
    simp [insertSort]
    have h : (insertSort.insert x (insertSort xs)).count n = (x :: insertSort xs).count n := by
      apply count_insert
    simp [h, ih]
where count_insert : ∀ (x : Int) (l : List Int) (n : Int), 
  (insertSort.insert x l).count n = (x :: l).count n := by
  intro x l n
  induction l with
  | nil => simp [insertSort.insert]
  | cons y ys ih =>
    simp [insertSort.insert]
    split_ifs with h_le
    · simp
    · simp [ih]

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
  let sorted_numbers := insertSort numbers_as_ints
  let sorted_words := sorted_numbers.map number_to_word_map
  " ".intercalate sorted_words

theorem correctness
(numbers: String)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use " ".intercalate (List.map number_to_word_map (insertSort (List.map (fun word => 
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
    | _ => -1) (numbers.splitOn " "))))
  constructor
  · rfl
  · intro h
    constructor
    · apply splitOn_intercalate_length
    constructor
    · intro n hn
      use n
      apply splitOn_intercalate_mem
      simp
      exact hn
    constructor
    · intro n hn
      use n
      apply mem_splitOn_intercalate at hn
      simp at hn
      exact hn
    constructor
    · intro n
      rw [← count_map_insertSort]
      simp
    · simp [is_sorted_asc_equiv]
      exact insertSort_sorted _