-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sol_equa (n : Nat) : List (List Nat) := sorry

/- The solutions to x² - 4y² = n are well-formed lists of pairs of natural numbers -/
-- </vc-definitions>

-- <vc-theorems>
theorem sol_equa_well_formed (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    (∀ pair ∈ result, pair.length = 2) := sorry
-- </vc-theorems>