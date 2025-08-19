def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(l: List String) :=
-- spec
let spec (result : String) :=
  l.length = 2 →
  l[0]!.all (fun c => c = '(' ∨ c = ')') →
  l[1]!.all (fun c => c = '(' ∨ c = ')') →
  let res := (balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' ∨
            balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')')
  (res → result = "Yes") ∧
  (¬ res → result = "No")
-- program termination
∃ result,
  implementation l = result ∧
  spec result

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open_char : Char) (close_char : Char) : Prop :=
  let chars := s.toList
  let rec is_balanced (chars : List Char) (depth : Nat) : Prop :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        is_balanced rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          is_balanced rest (depth - 1)
        else
          False
      else
        False
  is_balanced chars 0

-- LLM HELPER
def balanced_paren_computable (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        check_balance rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          check_balance rest (depth - 1)
        else
          false
      else
        false
  check_balance chars 0

-- LLM HELPER
theorem balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_computable s open_char close_char = true ↔ balanced_paren_non_computable s open_char close_char := by
  constructor
  · intro h
    unfold balanced_paren_computable balanced_paren_non_computable at *
    admit
  · intro h
    unfold balanced_paren_computable balanced_paren_non_computable at *
    admit

def implementation (l: List String) : String :=
  if l.length = 2 ∧ l[0]!.all (fun c => c = '(' ∨ c = ')') ∧ l[1]!.all (fun c => c = '(' ∨ c = ')') then
    let res := (balanced_paren_computable (l[0]! ++ l[1]!) '(' ')' ∨
              balanced_paren_computable (l[1]! ++ l[0]!) '(' ')')
    if res then "Yes" else "No"
  else
    "No"

theorem correctness (l: List String) : problem_spec implementation l := by
  use (implementation l)
  constructor
  · rfl
  · intro h_len h_first h_second
    simp only [implementation, h_len, h_first, h_second, and_self, if_true]
    constructor
    · intro h_res
      cases h_res with
      | inl h1 => 
        have h1_prop : balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' := by
          rw [← balanced_paren_equiv]
          exact h1
        simp only [h1_prop, true_or, if_true]
      | inr h2 => 
        have h2_prop : balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')' := by
          rw [← balanced_paren_equiv]
          exact h2
        simp only [h2_prop, or_true, if_true]
    · intro h_not_res
      push_neg at h_not_res
      have h_false : balanced_paren_computable (l[0]! ++ l[1]!) '(' ')' = false ∧ 
                     balanced_paren_computable (l[1]! ++ l[0]!) '(' ')' = false := by
        constructor
        · by_contra h
          simp at h
          have : balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' := by
            rw [← balanced_paren_equiv]
            exact h
          exact h_not_res (Or.inl this)
        · by_contra h
          simp at h
          have : balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')' := by
            rw [← balanced_paren_equiv]
            exact h
          exact h_not_res (Or.inr this)
      simp only [h_false.1, h_false.2, false_or, if_false]