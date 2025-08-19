import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def Rat : Type := ℚ

-- LLM HELPER
structure RatStruct where
  num : ℤ
  den : ℕ
  den_pos : den > 0

-- LLM HELPER
def RatStruct.add (a b : RatStruct) : RatStruct :=
  { num := a.num * b.den + b.num * a.den
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

-- LLM HELPER
instance : Add RatStruct := ⟨RatStruct.add⟩

-- LLM HELPER
def RatStruct.eq (a b : RatStruct) : Prop :=
  a.num * b.den = b.num * a.den

-- LLM HELPER
instance : DecidableEq RatStruct := fun a b => 
  if h : a.num * b.den = b.num * a.den then
    isTrue h
  else
    isFalse h

-- LLM HELPER
def problem_spec_helper (a b c : RatStruct) : Prop :=
  let nums := [a, b, c]
  ∃ i j k : ℕ, i < 3 ∧ j < 3 ∧ k < 3 ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ 
  (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ b.den = 1 ∧ c.den = 1

def problem_spec
(implementation: Rat → Rat → Rat → Bool)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Bool) :=
  result = true ↔ (a + b = c ∨ a + c = b ∨ b + c = a)
∃ result,
  implementation a b c = result ∧
  spec result

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  unfold problem_spec
  let spec := fun result => 
    result = true ↔ (a + b = c ∨ a + c = b ∨ b + c = a)
  
  use implementation a b c
  constructor
  · rfl
  · unfold implementation
    simp [spec]
    constructor
    · intro h
      exact h
    · intro h
      exact h