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
  simp [parseApples, String.join]
  sorry

-- LLM HELPER
lemma parseOranges_correct (x y : Nat) :
  parseOranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some y := by
  simp [parseOranges, String.join]
  sorry

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
    · use 0, 0
      constructor
      · simp
      · exfalso
        apply h
        use 0, 0
        simp [String.join]
        sorry