-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sorted (l : List Int) : Bool :=
  sorry

def solve_gift_distribution (n : Nat) (a b : List Int) : List Int × List Int :=
  sorry

def List.sort (l : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gift_distribution_output {n : Nat} {a b : List Int} :
  let (necklace, bracelet) := solve_gift_distribution n a b
  (necklace.sorted = true) ∧ (bracelet.sorted = true) := by
  sorry

theorem gift_distribution_nonempty {n : Nat} {a b : List Int} :
  let (necklace, bracelet) := solve_gift_distribution n a b
  necklace.length > 0 ∧ bracelet.length > 0 := by
  sorry

theorem gift_distribution_preserves_elements {n : Nat} {a b : List Int} :
  let (necklace, bracelet) := solve_gift_distribution n a b
  necklace = a.sort ∧ bracelet = b.sort := by
  sorry
-- </vc-theorems>