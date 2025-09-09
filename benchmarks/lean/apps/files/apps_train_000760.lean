def minimum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => (xs.foldl min x)

def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => (xs.foldl max x)

-- <vc-helpers>
-- </vc-helpers>

def min_poison_concentration (n : Nat) (concentrations : List Nat) : Nat :=
  sorry

theorem min_poison_concentration_bounds
  (n : Nat)
  (concentrations : List Nat)
  (h : 1 ≤ n)
  (h' : n ≤ concentrations.length)
  : min_poison_concentration n concentrations ≥ minimum concentrations ∧
    min_poison_concentration n concentrations ≤ maximum concentrations := by
  sorry

theorem min_poison_concentration_deterministic
  (n : Nat)
  (concentrations : List Nat)
  (h : 1 ≤ n)
  (h' : n ≤ concentrations.length)
  : min_poison_concentration n concentrations = min_poison_concentration n concentrations := by
  sorry

theorem min_poison_concentration_orderless
  (n : Nat)
  (concentrations : List Nat)
  (h : 1 ≤ n)
  (h' : n ≤ concentrations.length)
  : min_poison_concentration n concentrations = min_poison_concentration n concentrations.reverse := by
  sorry

theorem single_concentration_is_max
  (concentrations : List Nat)
  (h : 0 < concentrations.length)
  : min_poison_concentration 1 concentrations = maximum concentrations := by
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded