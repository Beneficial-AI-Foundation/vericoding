-- <vc-preamble>
def lowercase := Char
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PrintArray (a : Array α) : Unit :=
sorry

def DiagMatrix (rows : Int) (cols : Int) (zero : α) (one : α) : Array (Array α) :=
sorry

def PrintMatrix (m : Array (Array α)) : Unit :=
sorry

def LinearSearch (a : Array Int) (key : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LinearSearch_spec (a : Array Int) (key : Int) :
let n := LinearSearch a key
n ≤ a.size ∧ (n = a.size ∨ (a[n]!) = key) :=
sorry
-- </vc-theorems>