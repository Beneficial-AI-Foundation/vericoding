-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triangular_range (start stop : Int) : List (Int × Int) := sorry

theorem triangular_range_is_valid (start stop : Int) (h : stop ≥ start) :
  let result := triangular_range start stop
  ∀ (n tri : Int), (n, tri) ∈ result →
    (n > 0 ∧ 
     tri = (n * (n + 1)) / 2 ∧
     start ≤ tri ∧ tri ≤ stop) := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangular_range_single_point (n : Int) (h : n > 0) :
  let tri := (n * (n + 1)) / 2
  triangular_range tri tri = [(n, tri)] ∨ triangular_range tri tri = [] :=
sorry

theorem triangular_range_empty_invalid_range (start stop : Int) :
  stop < start → triangular_range start stop = [] :=
sorry

theorem triangular_range_empty_negative (start stop : Int) :
  stop < 0 → triangular_range start stop = [] :=
sorry
-- </vc-theorems>