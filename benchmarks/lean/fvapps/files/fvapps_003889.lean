-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isScientificNotation (s : String) : Bool :=
sorry

def sumProd (s : String) : String :=
sorry

def stringToFloat (s : String) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumProd_format {nums : List Float}
  (h1 : ∀ n ∈ nums, 0.1 ≤ n ∧ n ≤ 100)
  (h2 : 2 ≤ nums.length ∧ nums.length ≤ 4) :
  isScientificNotation (sumProd ("+".intercalate (nums.map toString))) :=
sorry

theorem sumProd_multiply (x y : Nat)
  (h1 : 1 ≤ x ∧ x ≤ 100)
  (h2 : 1 ≤ y ∧ y ≤ 100) :
  (stringToFloat (sumProd (s!"{x}*{y}"))) = Float.ofNat (x * y) :=
sorry

theorem sumProd_add (x y : Nat)
  (h1 : 1 ≤ x ∧ x ≤ 100)
  (h2 : 1 ≤ y ∧ y ≤ 100) :
  (stringToFloat (sumProd (s!"{x}+{y}"))) = Float.ofNat (x + y) :=
sorry
-- </vc-theorems>