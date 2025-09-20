-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def least_interval (tasks : List Char) (n : Nat) : Nat :=
  sorry

def countFrequencies (tasks : List Char) : List Nat :=
  sorry

def maxFrequency (tasks : List Char) : Nat :=
  sorry

def maxFrequencyCount (tasks : List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem least_interval_zero_cooldown (tasks : List Char) (h : tasks ≠ []) :
  least_interval tasks 0 = tasks.length :=
sorry

theorem least_interval_basic_properties (tasks : List Char) (n : Nat) (h : tasks ≠ []) :
  let result := least_interval tasks n
  let max_freq := maxFrequency tasks
  let max_freq_count := maxFrequencyCount tasks
  let min_possible := (max_freq - 1) * (n + 1) + max_freq_count
  result ≥ tasks.length ∧ result ≥ min_possible :=
sorry

theorem least_interval_upper_bound (tasks : List Char) (n : Nat) (h : tasks ≠ []) :
  least_interval tasks n ≤ tasks.length * (n + 1) :=
sorry
-- </vc-theorems>