def problem_spec
(implementation: String → Nat → Nat)
(string: String)
(n : Nat) :=
let spec (result: Nat) :=
∃ x y : Nat, x + y = n - result
∧ (String.join [x.repr, " apples and ", y.repr, " oranges"] = string)
∃ result, implementation string n = result ∧
spec result

-- LLM HELPER
def parseApples (s: String) : Option Nat :=
  let parts := s.splitOn " apples and "
  match parts with
  | [first, _] => first.toNat?
  | _ => none

-- LLM HELPER
def parseOranges (s: String) : Option Nat :=
  let parts := s.splitOn " apples and "
  match parts with
  | [_, second] => 
    let orangeParts := second.splitOn " oranges"
    match orangeParts with
    | [numStr, ""] => numStr.toNat?
    | _ => none
  | _ => none

def implementation (string: String) (n: Nat) : Nat :=
  match parseApples string, parseOranges string with
  | some x, some y => n - (x + y)
  | _, _ => 0

-- LLM HELPER
lemma parseApples_correct (x y : Nat) : 
  parseApples (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some x := by
  simp only [parseApples, String.join]
  have h : (x.repr ++ " apples and " ++ y.repr ++ " oranges").splitOn " apples and " = [x.repr, y.repr ++ " oranges"] := by
    rw [String.splitOn_append_left_eq_singleton_iff]
    simp
  rw [h]
  simp [Nat.repr_toNat]

-- LLM HELPER
lemma parseOranges_correct (x y : Nat) :
  parseOranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some y := by
  simp only [parseOranges, String.join]
  have h : (x.repr ++ " apples and " ++ y.repr ++ " oranges").splitOn " apples and " = [x.repr, y.repr ++ " oranges"] := by
    rw [String.splitOn_append_left_eq_singleton_iff]
    simp
  rw [h]
  simp
  have h2 : (y.repr ++ " oranges").splitOn " oranges" = [y.repr, ""] := by
    rw [String.splitOn_append_right_eq_singleton_iff]
    simp
  rw [h2]
  simp [Nat.repr_toNat]

-- LLM HELPER
lemma valid_format_parse (s : String) :
  (∃ x y : Nat, String.join [x.repr, " apples and ", y.repr, " oranges"] = s) →
  (∃ x y : Nat, parseApples s = some x ∧ parseOranges s = some y ∧ 
   String.join [x.repr, " apples and ", y.repr, " oranges"] = s) := by
  intro h
  obtain ⟨x, y, hxy⟩ := h
  use x, y
  constructor
  · rw [← hxy]; exact parseApples_correct x y
  constructor
  · rw [← hxy]; exact parseOranges_correct x y
  · exact hxy

theorem correctness
(s: String) (n : Nat)
: problem_spec implementation s n := by
  simp [problem_spec]
  use implementation s n
  constructor
  · rfl
  · simp [implementation]
    by_cases h : ∃ x y : Nat, String.join [x.repr, " apples and ", y.repr, " oranges"] = s
    · obtain ⟨x, y, hxy⟩ := h
      have h_parse := valid_format_parse s h
      obtain ⟨x', y', hx', hy', _⟩ := h_parse
      simp [hx', hy']
      use x', y'
      constructor
      · simp
      · rw [← hxy]
        have hx_eq : x' = x := by
          rw [← hxy] at hx'
          have := parseApples_correct x y
          rw [this] at hx'
          simp at hx'
          exact hx'
        have hy_eq : y' = y := by
          rw [← hxy] at hy'
          have := parseOranges_correct x y
          rw [this] at hy'
          simp at hy'
          exact hy'
        rw [hx_eq, hy_eq]
        exact hxy
    · cases h_parse : parseApples s with
      | none => 
        simp [h_parse]
        use 0, n
        simp
      | some x =>
        cases h_parse2 : parseOranges s with
        | none =>
          simp [h_parse, h_parse2]
          use 0, n
          simp
        | some y =>
          simp [h_parse, h_parse2]
          use 0, n
          simp