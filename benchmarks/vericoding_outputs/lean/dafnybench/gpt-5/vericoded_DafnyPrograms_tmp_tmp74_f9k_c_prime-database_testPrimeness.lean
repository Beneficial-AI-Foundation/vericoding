import Mathlib
-- <vc-preamble>
import Std

def prime (n : Nat) : Prop :=
n > 1 ∧ (∀ nr, 1 < nr → nr < n → n % nr ≠ 0)

inductive Answer where
| Yes : Answer
| No : Answer
| Unknown : Answer
deriving Repr

structure PrimeMap where
database : Std.HashMap Nat Bool

def PrimeMap.valid (pm : PrimeMap) : Prop :=
∀ i, pm.database.contains i →
(pm.database[i]! = true ↔ prime i)

def PrimeMap.new : PrimeMap :=
{ database := Std.HashMap.emptyWithCapacity 0 }
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
-- LLM HELPER
deriving instance DecidableEq for Answer
-- </vc-helpers>

-- <vc-definitions>
def PrimeMap.isPrime? (pm : PrimeMap) (n : Nat) : Answer :=
by
  classical
  exact
    if pm.database.contains n then
      if hp : prime n then Answer.Yes else Answer.No
    else
      Answer.Unknown

def testPrimeness (n : Nat) : Bool :=
by
  classical
  exact decide (prime n)
-- </vc-definitions>

-- <vc-theorems>
theorem PrimeMap.new_spec :
(PrimeMap.new).database.isEmpty :=
by
  decide

theorem PrimeMap.isPrime?_spec (pm : PrimeMap) (n : Nat) :
let result := pm.isPrime? n
(pm.database.contains n ∧ prime n ↔ result = Answer.Yes) ∧
(pm.database.contains n ∧ ¬prime n ↔ result = Answer.No) ∧
(¬pm.database.contains n ↔ result = Answer.Unknown) :=
by
  classical
  by_cases hc : pm.database.contains n
  ·
    by_cases hp : prime n
    ·
      constructor
      · simp [PrimeMap.isPrime?, hc, hp]
      constructor
      · simp [PrimeMap.isPrime?, hc, hp]
      · simp [PrimeMap.isPrime?, hc, hp]
    ·
      constructor
      · simp [PrimeMap.isPrime?, hc, hp]
      constructor
      · simp [PrimeMap.isPrime?, hc, hp]
      · simp [PrimeMap.isPrime?, hc, hp]
  ·
    constructor
    · simp [PrimeMap.isPrime?, hc]
    constructor
    · simp [PrimeMap.isPrime?, hc]
    · simp [PrimeMap.isPrime?, hc]

theorem testPrimeness_spec (n : Nat) :
n ≥ 0 → (testPrimeness n = true ↔ prime n) :=
by
  intro _h
  classical
  by_cases hp : prime n
  · simp [testPrimeness, hp]
  · simp [testPrimeness, hp]
-- </vc-theorems>
