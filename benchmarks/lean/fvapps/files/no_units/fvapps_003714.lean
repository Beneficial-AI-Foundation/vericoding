-- <vc-preamble>
def arr2bin (arr : List α) : String := sorry

def sumList (l : List Int) : Int := sorry

def toBinaryString (n : Int) : String := sorry

theorem arr2bin_all_ints {arr : List Int} :
  arr2bin arr = toBinaryString (sumList arr) := sorry

def allBinary (s : String) : Bool := sorry
def stringToNat (s : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAllInts (arr : List α) : Bool := sorry
def listToInts (arr : List α) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arr2bin_empty : 
  arr2bin ([] : List α) = "0" := sorry

theorem arr2bin_positive_ints {arr : List Nat} :
  let result := arr2bin arr
  allBinary result ∧
  stringToNat result = arr.foldl (init := 0) (·+·) := sorry

theorem arr2bin_mixed_types {α} {arr : List α} :
  (¬isAllInts arr → arr2bin arr = "") ∧
  (isAllInts arr → arr2bin arr = toBinaryString (sumList (listToInts arr))) := sorry
-- </vc-theorems>