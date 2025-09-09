-- <vc-helpers>
-- </vc-helpers>

def solve (n: Nat) (k: Nat) : String × String := sorry 

def stringToNat (s: String) : Nat := sorry

theorem solve_outputs_are_digits (n: Nat) (k: Nat)
    (h1: n ≥ 2) (h2: k ≥ 1) (h3: n ≤ 1000000) (h4: k ≤ 10) :
    let (first, last) := solve n k
    (∀ c ∈ first.data, '0' ≤ c ∧ c ≤ '9') ∧
    (∀ c ∈ last.data, '0' ≤ c ∧ c ≤ '9') := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible