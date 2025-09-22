-- <vc-preamble>
def sumList (l : List Int) : Int :=
  l.foldl (· + ·) 0

def toNat (i : Int) : Nat :=
  if i ≤ 0 then 0 else i.natAbs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortestSubarray (arr : List Int) (k : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_cases (k : Int) :
  shortestSubarray [] k = -1 ∧
  shortestSubarray [0] k = -1 ∧
  shortestSubarray [0,0] k = -1 :=
sorry

theorem positive_only (arr : List Int) (k : Int) (h1 : ∀ x ∈ arr, 0 < x) (h2 : 0 < k) :
  let result := shortestSubarray arr k
  if result = -1 then
    ∀ start len : Nat, start + len ≤ arr.length →
      sumList ((arr.take (start + len)).drop start) < k
  else
    (∃ start : Nat, start + (toNat result) ≤ arr.length ∧
      sumList ((arr.take (start + (toNat result))).drop start) ≥ k) ∧
    (∀ len : Nat, len < (toNat result) → ∀ start : Nat, start + len ≤ arr.length →
      sumList ((arr.take (start + len)).drop start) < k) :=
sorry

theorem result_bounds (arr : List Int) (k : Int) (h1 : 0 < k) (h2 : ¬arr.isEmpty) :
  let result := shortestSubarray arr k
  if result = -1 then True
  else 1 ≤ result ∧ result ≤ arr.length :=
sorry
-- </vc-theorems>