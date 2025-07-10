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
  | some x, some y => if x + y ≤ n then n - (x + y) else 0
  | _, _ => 0

-- LLM HELPER
lemma string_join_splitOn_apples (x y : Nat) :
  (String.join [x.repr, " apples and ", y.repr, " oranges"]).splitOn " apples and " = 
  [x.repr, y.repr ++ " oranges"] := by
  simp [String.join]
  sorry

-- LLM HELPER
lemma string_join_splitOn_oranges (y : Nat) :
  (y.repr ++ " oranges").splitOn " oranges" = [y.repr, ""] := by
  sorry

-- LLM HELPER
lemma parseApples_correct (x y : Nat) : 
  parseApples (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some x := by
  simp [parseApples]
  rw [string_join_splitOn_apples]
  simp [Nat.repr_toNat]

-- LLM HELPER
lemma parseOranges_correct (x y : Nat) :
  parseOranges (String.join [x.repr, " apples and ", y.repr, " oranges"]) = some y := by
  simp [parseOranges]
  rw [string_join_splitOn_apples]
  simp
  rw [string_join_splitOn_oranges]
  simp [Nat.repr_toNat]

-- LLM HELPER
lemma Nat.repr_toNat (n : Nat) : n.repr.toNat? = some n := by
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
      have hx : parseApples s = some x := by
        rw [← hxy]
        exact parseApples_correct x y
      have hy : parseOranges s = some y := by
        rw [← hxy]
        exact parseOranges_correct x y
      simp [hx, hy]
      by_cases hle : x + y ≤ n
      · simp [hle]
        use x, y
        constructor
        · simp
        · exact hxy
      · simp [hle]
        use 0, n
        simp
    · simp
      use 0, n
      simp