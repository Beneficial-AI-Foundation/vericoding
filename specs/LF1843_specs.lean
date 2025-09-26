-- <vc-preamble>
def Transaction.array (t : Transaction) : String := sorry

def find_invalid_transactions (trans : List String) : List String := sorry

def abs (n : Int) : Int := 
  if n < 0 then -n else n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitStr (s : String) : List String := sorry

theorem transaction_construction (name : String) (time amount : Int) (city : String) :
  let t := Transaction.mk name time amount city
  t.name = name ∧ 
  t.time = time ∧
  t.amount = amount ∧ 
  t.city = city := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>