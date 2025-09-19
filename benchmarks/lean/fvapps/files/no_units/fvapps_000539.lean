-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Nat) (k: Nat) : String × String := sorry 

def stringToNat (s: String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_outputs_are_digits (n: Nat) (k: Nat)
    (h1: n ≥ 2) (h2: k ≥ 1) (h3: n ≤ 1000000) (h4: k ≤ 10) :
    let (first, last) := solve n k
    (∀ c ∈ first.data, '0' ≤ c ∧ c ≤ '9') ∧
    (∀ c ∈ last.data, '0' ≤ c ∧ c ≤ '9') := sorry
-- </vc-theorems>