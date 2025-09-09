def riders (stations : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def calc_min_riders (stations: List Nat) : Nat :=
  sorry

theorem riders_positive (stations: List Nat) :
  stations.all (fun x => x > 0 ∧ x ≤ 100) →
  riders stations > 0 :=
sorry

theorem riders_bounded (stations: List Nat) :
  stations.all (fun x => x > 0 ∧ x ≤ 100) →
  riders stations ≤ stations.length + 1 :=
sorry

theorem riders_short_distances (stations: List Nat) :
  stations.all (fun x => x ≤ 1) →
  riders stations = 1 :=
sorry

theorem riders_long_distances (stations: List Nat) :
  stations.all (fun x => x ≥ 99 ∧ x ≤ 100) →
  (riders stations = stations.length ∨ riders stations = stations.length + 1) :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval riders [18, 15]

/-
info: 2
-/
-- #guard_msgs in
-- #eval riders [43, 23, 40, 13]

/-
info: 3
-/
-- #guard_msgs in
-- #eval riders [33, 8, 16, 47, 30, 30, 46]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible