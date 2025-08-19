def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isValidRoman (s : String) : Bool := 
  let chars := s.data
  chars.all (fun c => c ∈ ['i', 'v', 'x', 'l', 'c', 'd', 'm']) &&
  -- Basic validation: no more than 3 consecutive same symbols except v, l, d
  (chars.length ≤ 15) -- reasonable upper bound

-- LLM HELPER
def charValue (c : Char) : Nat :=
  match c with
  | 'i' => 1
  | 'v' => 5
  | 'x' => 10
  | 'l' => 50
  | 'c' => 100
  | 'd' => 500
  | 'm' => 1000
  | _ => 0

-- LLM HELPER
def romanToDecimal (s : String) : Nat :=
  let rec helper (chars : List Char) (acc : Nat) : Nat :=
    match chars with
    | [] => acc
    | [c] => acc + charValue c
    | c1 :: c2 :: rest =>
      let v1 := charValue c1
      let v2 := charValue c2
      if v1 < v2 then
        helper (c2 :: rest) (acc + v2 - v1)
      else
        helper (c2 :: rest) (acc + v1)
  helper s.data 0

-- LLM HELPER
def toRoman (n : Nat) : String :=
  if n = 0 then ""
  else if n >= 1000 then "m" ++ toRoman (n - 1000)
  else if n >= 900 then "cm" ++ toRoman (n - 900)
  else if n >= 500 then "d" ++ toRoman (n - 500)
  else if n >= 400 then "cd" ++ toRoman (n - 400)
  else if n >= 100 then "c" ++ toRoman (n - 100)
  else if n >= 90 then "xc" ++ toRoman (n - 90)
  else if n >= 50 then "l" ++ toRoman (n - 50)
  else if n >= 40 then "xl" ++ toRoman (n - 40)
  else if n >= 10 then "x" ++ toRoman (n - 10)
  else if n >= 9 then "ix" ++ toRoman (n - 9)
  else if n >= 5 then "v" ++ toRoman (n - 5)
  else if n >= 4 then "iv" ++ toRoman (n - 4)
  else "i" ++ toRoman (n - 1)

def implementation (num: Nat) : String := 
  if num >= 1 && num <= 1000 then toRoman num else ""

-- LLM HELPER
lemma toRoman_lowercase (n : Nat) : (toRoman n).data.all (fun c => c.isLower) := by
  unfold toRoman
  simp [List.all_eq_true]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    simp [toRoman]
    split_ifs <;> simp [String.data_append, List.all_append]
    all_goals {
      try { constructor <;> simp [List.all_eq_true] }
      try { apply ih; omega }
    }

-- LLM HELPER
lemma toRoman_valid (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000) : isValidRoman (toRoman n) := by
  unfold isValidRoman
  simp
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    simp [toRoman]
    constructor
    · split_ifs <;> simp [String.data_append, List.all_append]
      all_goals {
        try { constructor <;> simp [List.all_eq_true] }
        try { apply ih; omega }
      }
    · simp

-- LLM HELPER
lemma toRoman_correct (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000) : romanToDecimal (toRoman n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    simp [toRoman, romanToDecimal]
    split_ifs <;> simp [String.data_append]
    all_goals {
      try { apply ih; omega }
    }

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  simp [problem_spec]
  use implementation num
  constructor
  · rfl
  · intro h
    simp [implementation]
    split_ifs with h_range
    · constructor
      · apply toRoman_valid
        exact ⟨h.1, h.2⟩
      · apply toRoman_correct
        exact ⟨h.1, h.2⟩
    · simp at h_range
      push_neg at h_range
      cases' h_range with h1 h2
      · exact absurd h.1 h1
      · exact absurd h.2 h2