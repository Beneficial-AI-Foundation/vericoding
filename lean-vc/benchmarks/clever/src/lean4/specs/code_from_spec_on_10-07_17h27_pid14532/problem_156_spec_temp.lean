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
  let values := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
  let rec helper (remaining: Nat) (acc: String) (vals: List (Nat × String)) : String :=
    match vals with
    | [] => acc
    | (val, roman) :: rest =>
      if remaining >= val then
        helper (remaining - val) (acc ++ roman) vals
      else
        helper remaining acc rest
  termination_by remaining
  decreasing_by 
    simp_wf
    cases' vals with hd tl
    · cases' rest with val roman
      omega
    · cases' hd with val roman
      cases' rest with val2 roman2
      · omega
      · split_ifs with h
        · omega
        · omega
  if n = 0 then "" else helper n "" values

def implementation (num: Nat) : String := natToRoman num

-- LLM HELPER
lemma natToRoman_valid (n: Nat) (h: 1 ≤ n ∧ n ≤ 1000) : 
  isValidRoman (natToRoman n) ∧ romanToDecimal (natToRoman n) = n := by
  constructor
  · unfold isValidRoman natToRoman
    apply List.all_eq_true.mpr
    intro c hc
    simp [List.mem_cons, List.mem_singleton]
    by_cases h1 : c = 'i'
    · simp [h1]
    · by_cases h2 : c = 'v'
      · simp [h2]
      · by_cases h3 : c = 'x'
        · simp [h3]
        · by_cases h4 : c = 'l'
          · simp [h4]
          · by_cases h5 : c = 'c'
            · simp [h5]
            · by_cases h6 : c = 'd'
              · simp [h6]
              · simp [h1, h2, h3, h4, h5, h6]
  · unfold romanToDecimal natToRoman
    simp
    rfl

-- LLM HELPER
lemma natToRoman_lowercase (n: Nat) : 
  (natToRoman n).data.all (fun c => c.isLower) := by
  unfold natToRoman
  apply List.all_eq_true.mpr
  intro c hc
  simp [Char.isLower]
  by_cases h1 : c = 'i'
  · simp [h1]
  · by_cases h2 : c = 'v'
    · simp [h2]
    · by_cases h3 : c = 'x'
      · simp [h3]
      · by_cases h4 : c = 'l'
        · simp [h4]
        · by_cases h5 : c = 'c'
          · simp [h5]
          · by_cases h6 : c = 'd'
            · simp [h6]
            · by_cases h7 : c = 'm'
              · simp [h7]
              · simp [h1, h2, h3, h4, h5, h6, h7]

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  unfold problem_spec implementation
  use natToRoman num
  constructor
  · rfl
  · intro h
    constructor
    · have h_range : 1 ≤ num ∧ num ≤ 1000 := ⟨h.1, h.2.1⟩
      exact (natToRoman_valid num h_range).1
    · have h_range : 1 ≤ num ∧ num ≤ 1000 := ⟨h.1, h.2.1⟩
      exact (natToRoman_valid num h_range).2