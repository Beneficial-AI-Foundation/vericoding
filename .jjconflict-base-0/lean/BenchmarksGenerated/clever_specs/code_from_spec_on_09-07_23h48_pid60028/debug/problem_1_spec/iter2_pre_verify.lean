def problem_spec
-- function signature
(impl: String → List String)
-- inputs
(paren_string: String) :=
-- spec
let paren_string_filtered := (paren_string.toList.filter (fun c => c == '(' ∨  c == ')')).asString;
let spec (result_list: List String) :=
-- concat of result is input_filtered
(result_list.foldl (· ++ ·) "" = paren_string_filtered) ∧
-- each item in result is balanced and has only one group
(∀ str ∈ result_list, balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1);
-- program terminates
∃ result, impl paren_string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def balanced_paren_non_computable (s: String) (open_char: Char) (close_char: Char) : Prop :=
  let chars := s.toList
  let balance_at_pos := fun n => (chars.take n).count open_char - (chars.take n).count close_char
  (∀ i ∈ List.range chars.length, balance_at_pos (i + 1) ≥ 0) ∧ 
  balance_at_pos chars.length = 0

-- LLM HELPER
def count_paren_groups (s: String) : Nat :=
  let chars := s.toList
  let rec count_groups_aux (chars: List Char) (depth: Nat) (groups: Nat) : Nat :=
    match chars with
    | [] => groups
    | '(' :: rest => count_groups_aux rest (depth + 1) (if depth = 0 then groups + 1 else groups)
    | ')' :: rest => count_groups_aux rest (depth - 1) groups
    | _ :: rest => count_groups_aux rest depth groups
  count_groups_aux chars 0 0

-- LLM HELPER
def extract_balanced_groups (s: String) : List String :=
  let chars := s.toList.filter (fun c => c == '(' ∨ c == ')')
  let rec extract_aux (chars: List Char) (depth: Nat) (current: List Char) (acc: List String) : List String :=
    match chars with
    | [] => if current.isEmpty then acc else acc ++ [current.asString]
    | '(' :: rest => 
      let new_depth := depth + 1
      let new_current := current ++ ['(']
      extract_aux rest new_depth new_current acc
    | ')' :: rest =>
      let new_current := current ++ [')']
      if depth = 1 then
        extract_aux rest 0 [] (acc ++ [new_current.asString])
      else
        extract_aux rest (depth - 1) new_current acc
    | _ :: rest => extract_aux rest depth current acc
  extract_aux chars 0 [] []

def implementation (paren_string: String) : List String := 
  extract_balanced_groups paren_string

-- LLM HELPER
lemma extract_balanced_groups_correct (s: String) :
  let filtered := (s.toList.filter (fun c => c == '(' ∨ c == ')')).asString
  let result := extract_balanced_groups s
  (result.foldl (· ++ ·) "" = filtered) ∧
  (∀ str ∈ result, balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1) := by
  sorry

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  simp [problem_spec, implementation]
  use extract_balanced_groups paren_string
  constructor
  · rfl
  · exact extract_balanced_groups_correct paren_string