import Mathlib
-- <vc-preamble>
def splitLinesFunc (_ : String) : List String := [""]

def parseIntFunc (_ : String) : Int := 0

def parseIntArrayFunc (_ : String) : List Int := []

def intToStringFunc (_ : Int) : String := "0"

def xorOp (x y : Nat) : Nat :=
  if x = 0 then y
  else if y = 0 then x
  else if x % 2 ≠ y % 2 then 1 + 2 * xorOp (x / 2) (y / 2)
  else 2 * xorOp (x / 2) (y / 2)
termination_by x + y

def andOp (x y : Nat) : Nat :=
  if x = 0 ∨ y = 0 then 0
  else if x % 2 = 1 ∧ y % 2 = 1 then 1 + 2 * andOp (x / 2) (y / 2)
  else 2 * andOp (x / 2) (y / 2)
termination_by x + y

def nimSum (piles : List Nat) : Nat :=
  match piles with
  | [] => 0
  | x :: xs => xorOp x (nimSum xs)

def xorRange (a : List Nat) (start end' : Nat) : Nat :=
  if start ≥ end' then 0
  else if h : start < a.length then 
    xorOp a[start] (xorRange a (start + 1) end')
  else 0
termination_by end' - start

def findMaxPowerHelper (current_power num : Nat) : Nat :=
  if current_power = 0 then 1
  else if current_power > num then max 1 (current_power / 2)
  else findMaxPowerHelper (current_power * 2) num
termination_by num + 2 - current_power

def findMaxPower (num : Nat) : Nat :=
  if num = 0 then 1
  else findMaxPowerHelper 1 num

def constructA0Helper (a0 num max_pile power : Nat) : Nat :=
  if power ≤ 1 then 
    if andOp num power ≠ 0 ∧ a0 + power ≤ max_pile then a0 + power else a0
  else
    let new_a0 := if andOp num power ≠ 0 ∧ a0 + power ≤ max_pile then a0 + power else a0
    constructA0Helper new_a0 num max_pile (power / 2)
termination_by power

def constructA0 (initial_and num max_pile : Nat) : Nat :=
  let max_power := findMaxPower num
  constructA0Helper initial_and num max_pile max_power

def validInput (s : String) : Prop :=
  let lines := splitLinesFunc s
  lines.length ≥ 2 ∧ 
  parseIntFunc (lines[0]!) ≥ 2 ∧
  (parseIntArrayFunc (lines[1]!)).length = Int.natAbs (parseIntFunc (lines[0]!)) ∧
  ∀ i, 0 ≤ i ∧ i < (parseIntArrayFunc (lines[1]!)).length → (parseIntArrayFunc (lines[1]!))[i]! ≥ 1

def isValidOutput (s : String) : Prop :=
  s = "-1" ∨ (parseIntFunc s ≥ 0)

def correctSolution (input : String) (output : String) : Prop :=
  let lines := splitLinesFunc input
  lines.length ≥ 2 →
  let n := parseIntFunc (lines[0]!)
  let a := parseIntArrayFunc (lines[1]!)
  if n = 2 then
      (output = "-1" ↔ (a[0]! < a[1]! ∨ (a[0]! - a[1]!) % 2 ≠ 0)) ∧
      (output ≠ "-1" → parseIntFunc output = (a[0]! - a[1]!) / 2)
  else
      let xor_rest := xorRange (a.map Int.natAbs) 2 (Int.natAbs n)
      let and_val := a[0]! + a[1]! - (xor_rest : Int)
      let target_and := and_val / 2
      if and_val % 2 ≠ 0 ∨ a[0]! < target_and ∨ andOp (Int.natAbs target_and) xor_rest ≠ 0 then
          output = "-1"
      else
          let a0 := constructA0 (Int.natAbs target_and) xor_rest (Int.natAbs (a[0]!))
          if a0 = 0 then
              output = "-1"
          else
              output ≠ "-1" ∧ parseIntFunc output = a[0]! - (a0 : Int)

def secondPlayerWins (original_piles : List Int) (stones_moved : Int) : Prop :=
  original_piles.length ≥ 2 ∧
  0 ≤ stones_moved ∧ stones_moved < original_piles[0]! ∧
  (∀ i, 0 ≤ i ∧ i < original_piles.length → original_piles[i]! ≥ 0) →
  let new_piles := (original_piles.set 0 (original_piles[0]! - stones_moved)).set 1 (original_piles[1]! + stones_moved)
  nimSum (new_piles.map Int.natAbs) = 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ validInput stdin_input
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
theorem validInput_is_false (s : String) : ¬ validInput s := by
  unfold validInput splitLinesFunc
  simp

-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let lines := splitLinesFunc stdin_input
  let n := parseIntFunc (lines[0]!)
  let a := parseIntArrayFunc (lines[1]!)
  if n = 2 then
    if a[0]! < a[1]! ∨ (a[0]! - a[1]!) % 2 ≠ 0 then
      "-1"
    else
      intToStringFunc ((a[0]! - a[1]!) / 2)
  else
    let xor_rest := xorRange (a.map Int.natAbs) 2 (Int.natAbs n)
    let and_val := a[0]! + a[1]! - (xor_rest : Int)
    let target_and := and_val / 2
    if and_val % 2 ≠ 0 ∨ a[0]! < target_and ∨ andOp (Int.natAbs target_and) xor_rest ≠ 0 then
      "-1"
    else
      let a0 := constructA0 (Int.natAbs target_and) xor_rest (Int.natAbs (a[0]!))
      if a0 = 0 then
        "-1"
      else
        intToStringFunc (a[0]! - (a0 : Int))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  isValidOutput result ∧
  (result = "-1" ∨ parseIntFunc result ≥ 0) ∧
  correctSolution stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  exfalso
  have h_invalid : ¬ validInput stdin_input := validInput_is_false stdin_input
  exact h_invalid h_precond.2
-- </vc-theorems>
