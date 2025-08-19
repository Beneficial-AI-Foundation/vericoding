import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def isValidRoman (s: String) : Prop :=
  s.data.all (fun c => c ∈ ['i', 'v', 'x', 'l', 'c', 'd', 'm'])

-- LLM HELPER
def romanToDecimal (s: String) : Nat :=
  let rec helper (chars: List Char) (acc: Nat) : Nat :=
    match chars with
    | [] => acc
    | c :: rest =>
      let val := match c with
        | 'i' => 1
        | 'v' => 5
        | 'x' => 10
        | 'l' => 50
        | 'c' => 100
        | 'd' => 500
        | 'm' => 1000
        | _ => 0
      match rest with
      | [] => acc + val
      | next :: _ =>
        let nextVal := match next with
          | 'i' => 1
          | 'v' => 5
          | 'x' => 10
          | 'l' => 50
          | 'c' => 100
          | 'd' => 500
          | 'm' => 1000
          | _ => 0
        if val < nextVal then
          helper rest (acc - val)
        else
          helper rest (acc + val)
  helper s.data 0

-- LLM HELPER
def natToRoman (n: Nat) : String :=
  let rec helper (remaining: Nat) (acc: String) : String :=
    if remaining = 0 then acc
    else if remaining >= 1000 then helper (remaining - 1000) (acc ++ "m")
    else if remaining >= 900 then helper (remaining - 900) (acc ++ "cm")
    else if remaining >= 500 then helper (remaining - 500) (acc ++ "d")
    else if remaining >= 400 then helper (remaining - 400) (acc ++ "cd")
    else if remaining >= 100 then helper (remaining - 100) (acc ++ "c")
    else if remaining >= 90 then helper (remaining - 90) (acc ++ "xc")
    else if remaining >= 50 then helper (remaining - 50) (acc ++ "l")
    else if remaining >= 40 then helper (remaining - 40) (acc ++ "xl")
    else if remaining >= 10 then helper (remaining - 10) (acc ++ "x")
    else if remaining >= 9 then helper (remaining - 9) (acc ++ "ix")
    else if remaining >= 5 then helper (remaining - 5) (acc ++ "v")
    else if remaining >= 4 then helper (remaining - 4) (acc ++ "iv")
    else helper (remaining - 1) (acc ++ "i")
  helper n ""

def implementation (num: Nat) : String := natToRoman num

-- LLM HELPER
lemma natToRoman_valid (n: Nat) (h: 1 ≤ n ∧ n ≤ 1000) : 
  isValidRoman (natToRoman n) ∧ romanToDecimal (natToRoman n) = n := by
  sorry

-- LLM HELPER
lemma natToRoman_lowercase (n: Nat) : 
  (natToRoman n).data.all (fun c => c.isLower) := by
  sorry

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  unfold problem_spec implementation
  use natToRoman num
  constructor
  · rfl
  · intro h
    constructor
    · exact (natToRoman_valid num h).1
    · exact (natToRoman_valid num h).2