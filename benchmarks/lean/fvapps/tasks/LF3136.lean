-- <vc-preamble>
def listSum : List Nat → Nat
| [] => 0
| (x::xs) => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate : List Nat → Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_is_positive (cards : List Nat) :
  cards ≠ [] → calculate cards ≥ 0 :=
  sorry

theorem calc_single_element (cards : List Nat) (x : Nat) :
  cards = [x] → calculate cards = 2 * x :=
  sorry

theorem calc_increases_monotonic (cards : List Nat) (i : Nat) (hi : i < cards.length) :
  let cards' := cards.set i (cards[i]! + 1);
  calculate cards' ≥ calculate cards :=
  sorry

theorem calc_bounded_by_double (cards : List Nat) :
  cards ≠ [] → calculate cards ≤ listSum cards * (2 ^ cards.length) :=
  sorry
-- </vc-theorems>