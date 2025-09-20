-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def game (n : Nat) (health : List Nat) (laser_energy : Nat) : Nat :=
  sorry

def listMin (l : List Nat) : Nat :=
  sorry

def listSum (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_result_non_negative (n : Nat) (health : List Nat) (laser_energy : Nat) :
  game n health laser_energy ≥ 0 :=
sorry

theorem game_result_bounded (n : Nat) (health : List Nat) (laser_energy : Nat) :
  game n health laser_energy ≤ n :=
sorry

theorem game_empty_list (laser_energy : Nat) :
  game 0 [] laser_energy = 0 :=
sorry

theorem game_zero_energy (n : Nat) (health : List Nat) (h : health ≠ []) :
  game n health 0 = 0 :=
sorry

theorem game_energy_threshold (n : Nat) (health : List Nat) (laser_energy : Nat)
  (h1 : health ≠ []) (h2 : laser_energy < listMin health) :
  game n health laser_energy = 0 :=
sorry

theorem game_sufficient_energy (n : Nat) (health : List Nat) (h : health ≠ []) :
  game n health (2 * listSum health) = n :=
sorry
-- </vc-theorems>