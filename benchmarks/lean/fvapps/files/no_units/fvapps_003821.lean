-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def riders (stations: List Nat) (lost: Nat) : Nat := sorry

theorem riders_at_least_one {stations: List Nat} {lost: Nat}
  (h1: stations.length ≥ 2)
  (h2: 1 < lost)
  (h3: lost ≤ stations.length)
  (h4: ∀ x ∈ stations, x ≥ 1 ∧ x ≤ 100) :
  riders stations lost ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem riders_at_least_two {stations: List Nat} {lost: Nat}
  (h1: stations.length ≥ 2)
  (h2: 1 < lost)
  (h3: lost ≤ stations.length)
  (h4: ∀ x ∈ stations, x ≥ 1 ∧ x ≤ 100) :
  riders stations lost ≥ 2 := sorry

theorem riders_meets_minimum {stations: List Nat} {lost: Nat}
  (h1: stations.length ≥ 2)
  (h2: 1 < lost)
  (h3: lost ≤ stations.length)
  (h4: ∀ x ∈ stations, x ≥ 1 ∧ x ≤ 100) :
  let modified := (stations.take (lost-1)) ++ (stations.drop (lost-1))
  let min_riders := modified.foldr
    (fun d (acc : Nat × Nat) =>
      let (total, riders) := acc
      let new_total := total + d
      if new_total > 100 then (d, riders + 1)
      else (new_total, riders)) (0, 1)
  riders stations lost ≥ min_riders.2 := sorry
-- </vc-theorems>