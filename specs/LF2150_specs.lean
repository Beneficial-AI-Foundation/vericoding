-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_laser_sensors (n m k : Nat) (sensor_list : List (Nat × Nat)) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem laser_sensors_result_length {n m k : Nat} {sensor_list : List (Nat × Nat)} 
  (h1 : n ≥ 2) (h2 : m ≥ 2) (h3 : k = sensor_list.length)
  (h4 : ∀ (x y : Nat), (x,y) ∈ sensor_list → x < n ∧ y < m)
  : (solve_laser_sensors n m k sensor_list).length = k :=
sorry

theorem laser_sensors_result_values {n m k : Nat} {sensor_list : List (Nat × Nat)}
  (h1 : n ≥ 2) (h2 : m ≥ 2) (h3 : k = sensor_list.length)
  (h4 : ∀ (x y : Nat), (x,y) ∈ sensor_list → x < n ∧ y < m)
  : ∀ x ∈ solve_laser_sensors n m k sensor_list, x ≥ -1 :=
sorry

theorem laser_sensors_square_grid {n : Nat} 
  (h1 : n ≥ 3)
  (sensor_list := [(1,1), (1,n-1), (n-1,1), (n-1,n-1)])
  : (solve_laser_sensors n n 4 sensor_list).length = 4 :=
sorry
-- </vc-theorems>