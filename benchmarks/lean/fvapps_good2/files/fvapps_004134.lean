-- <vc-preamble>
def List.minimum (xs : List Float) : Float :=
  match xs with
  | [] => 0
  | x::rest => rest.foldl min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cubeTimes (times: List Float) : Float × Float := sorry

def List.sort (xs : List Float) : List Float :=
sorry

def Float.decimalPlaces (x : Float) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cubeTimes_avg_is_middle_three (times : List Float)
  (h : times.length = 5)
  (h2 : ∀ x ∈ times, 0.01 ≤ x ∧ x ≤ 1000) :
  let sorted := times.sort
  let middle_avg := (sorted[1]! + sorted[2]! + sorted[3]!) / 3
  (cubeTimes times).1 = Float.floor ((middle_avg * 100) + 0.5) / 100 :=
sorry

theorem cubeTimes_avg_decimal_places (times : List Float)
  (h : times.length = 5)
  (h2 : ∀ x ∈ times, 0.01 ≤ x ∧ x ≤ 1000) :
  let avg := (cubeTimes times).1
  Float.decimalPlaces avg ≤ 2 :=
sorry

theorem cubeTimes_fastest_is_min (times : List Float)
  (h : times.length = 5)
  (h2 : ∀ x ∈ times, 0.01 ≤ x ∧ x ≤ 1000) :
  (cubeTimes times).2 = List.minimum times :=
sorry
-- </vc-theorems>