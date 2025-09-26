-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_time (speeds: List Int) : Int :=
  sorry

def List.sorted (l: List Int) : List Int :=
  sorry

def isPermutation (l1 l2: List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_time_positive (speeds: List Int)
  (h: speeds.length = 4)
  (h2: ∀ x ∈ speeds, x ≥ 1) :
  shortest_time speeds > 0 :=
sorry

theorem shortest_time_min_bound (speeds: List Int)
  (h: speeds.length = 4)
  (h2: ∀ x ∈ speeds, x ≥ 1) :
  let sorted := speeds.sorted
  shortest_time speeds ≥ sorted[0]! + sorted[1]! + sorted[3]! :=
sorry

theorem shortest_time_two_crossings (speeds: List Int)
  (h: speeds.length = 4)
  (h2: ∀ x ∈ speeds, x ≥ 1) :
  let sorted := speeds.sorted
  shortest_time speeds ≥ 2 * (sorted[0]! + sorted[1]!) :=
sorry

theorem shortest_time_order_invariant (speeds1 speeds2: List Int)
  (h1: speeds1.length = 4)
  (h2: speeds2.length = 4)
  (h3: ∀ x ∈ speeds1, x ≥ 1)
  (h4: ∀ x ∈ speeds2, x ≥ 1)
  (h5: isPermutation speeds1 speeds2) :
  shortest_time speeds1 = shortest_time speeds2 :=
sorry

theorem shortest_time_monotonic (speeds: List Int)
  (h: speeds.length = 4)
  (h2: ∀ x ∈ speeds, x ≥ 1)
  (i: Nat)
  (h3: i < speeds.length) :
  let increased := speeds.set i (speeds[i]! + 1)
  shortest_time increased ≥ shortest_time speeds :=
sorry
-- </vc-theorems>