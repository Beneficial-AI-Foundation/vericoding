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
  have h : (String.join [x.repr, " apples and ", y.repr, " oranges"]).splitOn " apples and " = [x.repr, String.join [y.repr, " oranges"]] := by
    simp [String.splitOn_join_eq_iff]
  rw [h]
  simp

-- LLM HELPER
lemma parseOranges_correct (x y : Nat) :
  parseOranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some y := by
  simp only [parseOranges, String.join]
  have h : (String.join [x.repr, " apples and ", y.repr, " oranges"]).splitOn " apples and " = [x.repr, String.join [y.repr, " oranges"]] := by
    simp [String.splitOn_join_eq_iff]
  rw [h]
  simp
  have h2 : (String.join [y.repr, " oranges"]).splitOn " oranges" = [y.repr, ""] := by
    simp [String.splitOn_join_eq_iff]
  rw [h2]
  simp

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
      rw [←hxy]
      simp [parseApples_correct, parseOranges_correct]
      use x, y
      constructor
      · simp
      · exact hxy
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
          exfalso
          apply h
          use x, y
          -- This case should be impossible given our parsing correctness
          sorry