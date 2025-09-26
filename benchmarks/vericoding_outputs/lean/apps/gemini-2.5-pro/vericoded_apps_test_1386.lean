import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  ∃ i, 0 < i ∧ i < input.length - 1 ∧ input.data[i]! = ' ' ∧
  (∀ j, 0 ≤ j ∧ j < i → '0' ≤ input.data[j]! ∧ input.data[j]! ≤ '9') ∧
  (∀ j, i < j ∧ j < input.length → '0' ≤ input.data[j]! ∧ input.data[j]! ≤ '9')

def ValidDimensions (w h : Int) : Prop :=
  w ≥ 1 ∧ h ≥ 1 ∧ w ≤ 1000 ∧ h ≤ 1000

partial def FindSpace (s : String) (start : Nat) : Nat :=
  if start < s.length then
    if s.data[start]! = ' ' then start
    else FindSpace s (start + 1)
  else start

partial def StringToInt (s : String) : Int :=
  if s.length = 1 then 
    (s.data[0]!.toNat - '0'.toNat : Int)
  else 
    StringToInt (s.take (s.length - 1)) * 10 + (s.data[s.length - 1]!.toNat - '0'.toNat : Int)

def ParseTwoInts (input : String) : Int × Int :=
  let spaceIndex := FindSpace input 0
  let w := StringToInt (input.take spaceIndex)
  let h := StringToInt (input.drop (spaceIndex + 1))
  (w, h)

partial def IntToString (n : Int) : String :=
  if n = 0 then "0"
  else if n < 10 then String.mk [Char.ofNat ('0'.toNat + n.natAbs)]
  else IntToString (n / 10) ++ IntToString (n % 10)

partial def ModPow (base exp mod : Int) : Int :=
  if exp = 0 then 1 % mod
  else if exp % 2 = 0 then
    let half := ModPow base (exp / 2) mod
    (half * half) % mod
  else
    (base * ModPow base (exp - 1) mod) % mod

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input ∧
  let (w, h) := ParseTwoInts input
  ValidDimensions w h
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def M : Int := 998244353

-- LLM HELPER
lemma helper_mod_pos : M > 0 := by native_decide

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let (w, h) := ParseTwoInts input
  let pow_w := ModPow 2 w M
  let pow_h := ModPow 2 h M
  let count := (pow_w + pow_h - 2) % M
  IntToString count
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ∃ count : Int, count ≥ 0 ∧ count < 998244353 ∧ result = IntToString count

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve, solve_postcond, M]
  let (w, h) := ParseTwoInts input
  use (ModPow 2 w M + ModPow 2 h M - 2) % M
  simp [M]
  constructor
  . apply Int.emod_nonneg
    linarith [helper_mod_pos]
  . apply Int.emod_lt_of_pos
    exact helper_mod_pos
-- </vc-theorems>
