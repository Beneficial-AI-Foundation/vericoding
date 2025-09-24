-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cooking_time (n: Nat) (times: List Nat) : Nat :=
  sorry

def list_maximum (l: List Nat) : Nat :=
  sorry

def list_sorted_take (l: List Nat) (n: Nat) : List Nat :=
  sorry

def list_sum (l: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cooking_time_lower_bound_half_sum {n: Nat} {times: List Nat}
  (h1: 1 ≤ n) (h2: n ≤ 100) (h3: times.length ≥ 1) :
  let usedTimes := list_sorted_take times (min n times.length)
  min_cooking_time n times ≥ (list_sum usedTimes) / 2 := by
  sorry

theorem min_cooking_time_lower_bound_max {n: Nat} {times: List Nat}
  (h1: 1 ≤ n) (h2: n ≤ 100) (h3: times.length ≥ 1) :
  min_cooking_time n times ≥ list_maximum (times.take n) := by
  sorry

theorem min_cooking_time_upper_bound_sum {n: Nat} {times: List Nat}
  (h1: 1 ≤ n) (h2: n ≤ 100) (h3: times.length ≥ 1) :
  let usedTimes := list_sorted_take times (min n times.length)
  min_cooking_time n times ≤ list_sum usedTimes := by
  sorry

theorem min_cooking_time_equal_times {n: Nat} (h1: 1 ≤ n) (h2: n ≤ 100) :
  let times := List.replicate n 10
  min_cooking_time n times = ((n + 1) / 2) * 10 := by
  sorry

theorem min_cooking_time_single_item {times: List Nat} (h: times.length ≥ 1) :
  min_cooking_time 1 times = list_maximum times := by
  sorry
-- </vc-theorems>