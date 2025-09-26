import Mathlib
-- <vc-preamble>
partial def RecursivePositiveProduct (q : Array Int) : Int :=
if q.size = 0 then 1
else if q[0]! ≤ 0 then RecursivePositiveProduct (q.extract 1 q.size)
else q[0]! * RecursivePositiveProduct (q.extract 1 q.size)
partial def RecursiveCount (key : Int) (q : Array Int) : Int :=
if q.size = 0 then 0
else if q[q.size - 1]! = key then
1 + RecursiveCount key (q.extract 0 (q.size - 1))
else RecursiveCount key (q.extract 0 (q.size - 1))
def county (elem : Int) (key : Int) : Int :=
if elem = key then 1 else 0
def prody (elem : Int) : Int :=
if elem ≤ 0 then 1 else elem
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance instCoeIntNat : Coe Int Nat where
  coe := Int.toNat
-- </vc-helpers>

-- <vc-definitions>
def ProdAndCount (q : Array Int) (key : Int) : Int × Nat :=
(RecursivePositiveProduct q, Int.toNat (RecursiveCount key q))
-- </vc-definitions>

-- <vc-theorems>
theorem ProdAndCount_spec (q : Array Int) (key : Int) :
let (prod, count) := ProdAndCount q key
prod = RecursivePositiveProduct q ∧
count = RecursiveCount key q :=
by
  simpa [ProdAndCount] using And.intro rfl rfl
-- </vc-theorems>
