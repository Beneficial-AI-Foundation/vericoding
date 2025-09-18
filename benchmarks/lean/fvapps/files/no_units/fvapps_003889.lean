-- <vc-preamble>
def isScientificNotation (s : String) : Bool := sorry

def sumProd (s : String) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringToFloat (s : String) : Float := sorry 

theorem sumProd_format {nums : List Float} 
  (h1 : ∀ n ∈ nums, 0.1 ≤ n ∧ n ≤ 100) 
  (h2 : 2 ≤ nums.length ∧ nums.length ≤ 4) : 
  isScientificNotation (sumProd ("+".intercalate (nums.map toString))) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumProd_multiply (x y : Nat)
  (h1 : 1 ≤ x ∧ x ≤ 100)
  (h2 : 1 ≤ y ∧ y ≤ 100) :
  (stringToFloat (sumProd (s!"{x}*{y}"))) = Float.ofNat (x * y) := sorry

theorem sumProd_add (x y : Nat)
  (h1 : 1 ≤ x ∧ x ≤ 100)
  (h2 : 1 ≤ y ∧ y ≤ 100) :
  (stringToFloat (sumProd (s!"{x}+{y}"))) = Float.ofNat (x + y) := sorry
-- </vc-theorems>