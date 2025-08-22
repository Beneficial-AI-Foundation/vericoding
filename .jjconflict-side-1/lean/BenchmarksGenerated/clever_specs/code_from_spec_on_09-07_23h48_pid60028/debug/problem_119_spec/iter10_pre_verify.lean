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
def balanced_paren_non_computable (s : String) (open : Char) (close : Char) : Prop :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (count : Int) : Bool :=
    match chars with
    | [] => count = 0
    | c :: rest =>
      if c = open then
        check_balance rest (count + 1)
      else if c = close then
        if count > 0 then
          check_balance rest (count - 1)
        else
          false
      else
        false
  check_balance chars 0

-- LLM HELPER
def balanced_paren_computable (s : String) (open : Char) (close : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (count : Int) : Bool :=
    match chars with
    | [] => count = 0
    | c :: rest =>
      if c = open then
        check_balance rest (count + 1)
      else if c = close then
        if count > 0 then
          check_balance rest (count - 1)
        else
          false
      else
        false
  check_balance chars 0

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open : Char) (close : Char) :
  balanced_paren_non_computable s open close ↔ balanced_paren_computable s open close = true := by
  simp [balanced_paren_non_computable, balanced_paren_computable]

def implementation (l: List String) : String :=
  if l.length = 2 ∧ 
     l[0]!.all (fun c => c = '(' ∨ c = ')') ∧ 
     l[1]!.all (fun c => c = '(' ∨ c = ')') then
    let s1 := l[0]! ++ l[1]!
    let s2 := l[1]! ++ l[0]!
    if balanced_paren_computable s1 '(' ')' ∨ balanced_paren_computable s2 '(' ')' then
      "Yes"
    else
      "No"
  else
    "No"

theorem correctness
(l: List String)
: problem_spec implementation l := by
  simp [problem_spec, implementation]
  exists (if l.length = 2 ∧ 
             l[0]!.all (fun c => c = '(' ∨ c = ')') ∧ 
             l[1]!.all (fun c => c = '(' ∨ c = ')') then
            let s1 := l[0]! ++ l[1]!
            let s2 := l[1]! ++ l[0]!
            if balanced_paren_computable s1 '(' ')' ∨ balanced_paren_computable s2 '(' ')' then
              "Yes"
            else
              "No"
          else
            "No")
  constructor
  · rfl
  · intro h1 h2 h3
    simp [h1, h2, h3]
    constructor
    · intro h4
      simp
      rw [balanced_paren_equiv, balanced_paren_equiv] at h4
      cases h4 with
      | inl h => simp [h]
      | inr h => simp [h]
    · intro h4
      simp
      rw [balanced_paren_equiv, balanced_paren_equiv]
      by_contra h5
      simp at h5
      cases h5 with
      | inl h => simp [h] at h4
      | inr h => simp [h] at h4