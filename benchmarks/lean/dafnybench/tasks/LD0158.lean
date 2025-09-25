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
-- </vc-helpers>

-- <vc-definitions>
def PrimeMap.isPrime? (pm : PrimeMap) (n : Nat) : Answer :=
sorry

def testPrimeness (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem PrimeMap.new_spec :
(PrimeMap.new).database.isEmpty :=
sorry

theorem PrimeMap.isPrime?_spec (pm : PrimeMap) (n : Nat) :
let result := pm.isPrime? n
(pm.database.contains n ∧ prime n ↔ result = Answer.Yes) ∧
(pm.database.contains n ∧ ¬prime n ↔ result = Answer.No) ∧
(¬pm.database.contains n ↔ result = Answer.Unknown) :=
sorry

theorem testPrimeness_spec (n : Nat) :
n ≥ 0 → (testPrimeness n = true ↔ prime n) :=
sorry
-- </vc-theorems>