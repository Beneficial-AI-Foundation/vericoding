-- <vc-preamble>
def count_odd_frequencies (weights : List Nat) : Nat :=
  let freqs := weights.foldl (fun acc x =>
    match acc.find? (fun p => p.1 = x) with
    | some p => acc.erase p ++ [(p.1, p.2 + 1)]
    | none => acc ++ [(x, 1)]
    ) []
  (freqs.filter (fun p => p.2 % 2 = 1)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_steps_to_lift (n : Nat) (weights : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_steps_nonneg (n : Nat) (weights : List Nat) :
  min_steps_to_lift n weights ≥ 0 :=
sorry

theorem min_steps_upper_bound (n : Nat) (weights : List Nat) :
  min_steps_to_lift n weights ≤ n :=
sorry

theorem min_steps_odd_freq_bound (n : Nat) (weights : List Nat) :
  min_steps_to_lift n weights ≥ count_odd_frequencies weights :=
sorry
-- </vc-theorems>