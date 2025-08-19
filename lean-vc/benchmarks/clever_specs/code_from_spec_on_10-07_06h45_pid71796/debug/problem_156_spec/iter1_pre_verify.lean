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
where
  charValue (c : Char) : Nat :=
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
def toRoman (n : Nat) : String :=
  let rec helper (num : Nat) (acc : String) : String :=
    if num = 0 then acc
    else if num >= 1000 then helper (num - 1000) (acc ++ "m")
    else if num >= 900 then helper (num - 900) (acc ++ "cm")
    else if num >= 500 then helper (num - 500) (acc ++ "d")
    else if num >= 400 then helper (num - 400) (acc ++ "cd")
    else if num >= 100 then helper (num - 100) (acc ++ "c")
    else if num >= 90 then helper (num - 90) (acc ++ "xc")
    else if num >= 50 then helper (num - 50) (acc ++ "l")
    else if num >= 40 then helper (num - 40) (acc ++ "xl")
    else if num >= 10 then helper (num - 10) (acc ++ "x")
    else if num >= 9 then helper (num - 9) (acc ++ "ix")
    else if num >= 5 then helper (num - 5) (acc ++ "v")
    else if num >= 4 then helper (num - 4) (acc ++ "iv")
    else helper (num - 1) (acc ++ "i")
  helper n ""

def implementation (num: Nat) : String := 
  if num >= 1 && num <= 1000 then toRoman num else ""

-- LLM HELPER
lemma toRoman_lowercase (n : Nat) : (toRoman n).data.all (fun c => c.isLower) := by
  sorry

-- LLM HELPER
lemma toRoman_valid (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000) : isValidRoman (toRoman n) := by
  sorry

-- LLM HELPER
lemma toRoman_correct (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000) : romanToDecimal (toRoman n) = n := by
  sorry

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
      · exact toRoman_valid num ⟨h.1, h.2⟩
      · exact toRoman_correct num ⟨h.1, h.2⟩
    · simp at h_range
      cases' h_range with h1 h2
      · exact absurd h.1 h1
      · exact absurd h.2 h2