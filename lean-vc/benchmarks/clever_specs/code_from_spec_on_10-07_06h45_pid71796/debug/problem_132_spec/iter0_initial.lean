def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
string.toList.all (fun x => x = '(' ∨ x = ')') →
result = true ↔
  ∃ x : String,
    is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x
-- program termination
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_subsequence (sub main : List Char) : Bool :=
  match sub, main with
  | [], _ => true
  | _, [] => false
  | h1::t1, h2::t2 => 
    if h1 = h2 then is_subsequence t1 t2
    else is_subsequence sub t2

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open close : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (lst : List Char) (depth : Int) : Bool :=
    match lst with
    | [] => depth = 0
    | h::t => 
      if h = open then check_balance t (depth + 1)
      else if h = close then 
        if depth > 0 then check_balance t (depth - 1)
        else false
      else check_balance t depth
  check_balance chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Int :=
  let chars := s.toList
  let rec compute_depth (lst : List Char) (current_depth max_depth : Int) : Int :=
    match lst with
    | [] => max_depth
    | h::t => 
      if h = '(' then 
        let new_depth := current_depth + 1
        compute_depth t new_depth (max new_depth max_depth)
      else if h = ')' then
        compute_depth t (current_depth - 1) max_depth
      else
        compute_depth t current_depth max_depth
  compute_depth chars 0 0

-- LLM HELPER
def has_balanced_subsequence_with_depth (s : String) : Bool :=
  let chars := s.toList
  let parens_only := chars.filter (fun c => c = '(' ∨ c = ')')
  
  -- Try all possible subsequences
  let rec try_subsequences (remaining : List Char) (current : List Char) : Bool :=
    match remaining with
    | [] => 
      let subseq_str := String.mk current
      balanced_paren_non_computable subseq_str '(' ')' ∧ 
      2 ≤ count_max_paren_depth subseq_str
    | h::t =>
      -- Try including current character
      (try_subsequences t (current ++ [h])) ∨
      -- Try excluding current character  
      (try_subsequences t current)
  
  try_subsequences parens_only []

def implementation (lst: String) : Bool := 
  has_balanced_subsequence_with_depth lst

-- LLM HELPER
lemma subsequence_correctness (sub main : List Char) : 
  is_subsequence sub main = true ↔ ∃ indices, sub.length = indices.length ∧ 
  ∀ i j, i < j → i < indices.length → j < indices.length → 
  indices.get ⟨i, by sorry⟩ < indices.get ⟨j, by sorry⟩ ∧
  ∀ k, k < sub.length → sub.get ⟨k, by sorry⟩ = main.get ⟨indices.get ⟨k, by sorry⟩, by sorry⟩ := by
  sorry

-- LLM HELPER
lemma balanced_paren_correctness (s : String) :
  balanced_paren_non_computable s '(' ')' = true ↔ 
  ∃ depth_sequence : List Int, 
    depth_sequence.length = s.length + 1 ∧
    depth_sequence.head? = some 0 ∧
    depth_sequence.getLast? = some 0 ∧
    ∀ i, i < s.length → depth_sequence.get! i ≥ 0 := by
  sorry

-- LLM HELPER
lemma depth_count_correctness (s : String) :
  count_max_paren_depth s = 
  (s.toList.scanl (fun acc c => if c = '(' then acc + 1 else if c = ')' then acc - 1 else acc) 0).maximum?.getD 0 := by
  sorry

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  unfold implementation
  use has_balanced_subsequence_with_depth string
  constructor
  · rfl
  · intro spec_result
    intro h_all_parens
    constructor
    · intro h_true
      unfold has_balanced_subsequence_with_depth at h_true
      sorry -- Need to extract witness from the computation
    · intro h_exists
      unfold has_balanced_subsequence_with_depth
      sorry -- Need to show the algorithm finds the subsequence