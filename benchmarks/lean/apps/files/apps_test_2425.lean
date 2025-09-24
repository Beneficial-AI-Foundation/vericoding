-- <vc-preamble>
def power2 (k : Nat) : Nat :=
  if k = 0 then 1 else 2 * power2 (k - 1)

def ValidQuery (a : Int) : Prop :=
  2 ≤ a ∧ a ≤ power2 25 - 1

def ValidQueries (queries : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < queries.length → ValidQuery (queries[i]!)

axiom largestProperDivisorHelper : Nat → Nat → Nat

axiom largestProperDivisor : Nat → Nat

def ValidResults (queries : List Int) (results : List Int) : Prop :=
  results.length = queries.length ∧
  (∀ i, 0 ≤ i ∧ i < results.length → results[i]! ≥ 1) ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → 
    (∃ c, 1 ≤ c ∧ c ≤ 26 ∧ power2 c - 1 ≥ queries[i]!.natAbs ∧ 
     (c = 1 ∨ power2 (c-1) - 1 < queries[i]!.natAbs) ∧
     (power2 c - 1 > queries[i]!.natAbs → results[i]! = power2 c - 1) ∧
     (power2 c - 1 = queries[i]!.natAbs → 
       results[i]! = (if power2 c - 1 ≤ 1 then 1 else largestProperDivisor (power2 c - 1)))))

@[reducible, simp]
def solve_precond (queries : List Int) : Prop :=
  ValidQueries queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (queries : List Int) (h_precond : solve_precond queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries : List Int) (results : List Int) (h_precond : solve_precond queries) : Prop :=
  ValidResults queries results

theorem solve_spec_satisfied (queries : List Int) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  sorry
-- </vc-theorems>