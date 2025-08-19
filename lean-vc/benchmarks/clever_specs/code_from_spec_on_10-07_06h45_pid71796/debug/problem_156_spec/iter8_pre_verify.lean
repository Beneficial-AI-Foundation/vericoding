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
  let rec helper (n : Nat) (fuel : Nat) : String :=
    if fuel = 0 then ""
    else if n = 0 then ""
    else if n >= 1000 then "m" ++ helper (n - 1000) (fuel - 1)
    else if n >= 900 then "cm" ++ helper (n - 900) (fuel - 1)
    else if n >= 500 then "d" ++ helper (n - 500) (fuel - 1)
    else if n >= 400 then "cd" ++ helper (n - 400) (fuel - 1)
    else if n >= 100 then "c" ++ helper (n - 100) (fuel - 1)
    else if n >= 90 then "xc" ++ helper (n - 90) (fuel - 1)
    else if n >= 50 then "l" ++ helper (n - 50) (fuel - 1)
    else if n >= 40 then "xl" ++ helper (n - 40) (fuel - 1)
    else if n >= 10 then "x" ++ helper (n - 10) (fuel - 1)
    else if n >= 9 then "ix" ++ helper (n - 9) (fuel - 1)
    else if n >= 5 then "v" ++ helper (n - 5) (fuel - 1)
    else if n >= 4 then "iv" ++ helper (n - 4) (fuel - 1)
    else "i" ++ helper (n - 1) (fuel - 1)
  helper n 1000

def implementation (num: Nat) : String := 
  if num >= 1 && num <= 1000 then toRoman num else ""

-- LLM HELPER
lemma toRoman_valid (n : Nat) : isValidRoman (toRoman n) = true := by
  unfold isValidRoman toRoman
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro x hx
    unfold toRoman.helper at hx
    simp at hx
    tauto
  · simp

-- LLM HELPER
lemma toRoman_correct (n : Nat) (h : 1 ≤ n ∧ n ≤ 1000) : romanToDecimal (toRoman n) = n := by
  unfold romanToDecimal toRoman
  simp only [charValue]
  unfold toRoman.helper
  simp
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp [romanToDecimal.helper]
    split_ifs <;> simp [charValue] <;> omega

-- LLM HELPER
lemma toRoman_lowercase (n : Nat) : (toRoman n).data.all (fun c => c.isLower) = true := by
  unfold toRoman
  simp only [List.all_eq_true]
  intro x hx
  unfold toRoman.helper at hx
  simp at hx
  tauto

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h
    unfold implementation
    split_ifs with h_range
    · constructor
      · exact toRoman_valid num
      · exact toRoman_correct num ⟨h.1, h.2.1⟩
    · simp at h_range
      push_neg at h_range
      cases' h_range with h1 h2
      · exact absurd h.1 h1
      · exact absurd h.2.1 h2