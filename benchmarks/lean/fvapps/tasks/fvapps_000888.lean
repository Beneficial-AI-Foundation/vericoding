-- <vc-preamble>
def fst_minus (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat :=
sorry

def list_sum (l : List Nat) : Nat :=
sorry

def min_delivery_time (n m k : Nat) (deliveries : List (Nat × Nat × Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_delivery_time_non_negative (n m k : Nat) (deliveries : List (Nat × Nat × Nat × Nat)) :
  min_delivery_time n m k deliveries ≥ 0 :=
sorry

theorem min_delivery_time_same_point (n : Nat) :
  let m := n
  let deliveries := [(1,1,1,1)]
  min_delivery_time n m 1 deliveries = 0 :=
sorry

theorem min_delivery_time_bounded (n m k : Nat) (deliveries : List (Nat × Nat × Nat × Nat)) :
  min_delivery_time n m k deliveries ≤
    list_sum (deliveries.map (fun (d: Nat × Nat × Nat × Nat) =>
      let (x1, y1, x2, y2) := d
      2 * (fst_minus x1 x2 + fst_minus y1 y2))) :=
sorry
-- </vc-theorems>