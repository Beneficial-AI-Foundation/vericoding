-- <vc-preamble>
def tower_defense (grid : Array String) (turrets : List (Char × TurretInfo)) 
                  (wave : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Int → Int 
  | [] => 0
  | x::xs => x + list_sum xs

/- The tower_defense function returns a non-negative integer result -/
-- </vc-definitions>

-- <vc-theorems>
theorem tower_defense_returns_nonneg (grid : Array String) 
        (turrets : List (Char × TurretInfo)) (wave : List Int)
        (h : turrets.length > 0) :
  0 ≤ tower_defense grid turrets wave := sorry

/- The tower_defense result is at most the sum of the wave numbers -/

theorem tower_defense_leq_wave_sum (grid : Array String)
        (turrets : List (Char × TurretInfo)) (wave : List Int)  
        (h : turrets.length > 0) :
  tower_defense grid turrets wave ≤ list_sum wave := sorry

/- The tower_defense function returns 0 for an empty wave -/ 

theorem tower_defense_empty_wave (grid : Array String)
        (turrets : List (Char × TurretInfo))
        (h : turrets.length > 0) :
  tower_defense grid turrets [] = 0 := sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval tower_defense #["0111111", "  A  B1", " 111111", " 1     ", " 1C1111", " 111 D1", "      1"] {"A": [3, 2], "B": [1, 4], "C": [2, 2], "D": [1, 3]} #[30, 14, 27, 21, 13, 0, 15, 17, 0, 18, 26]

/-
info: 16
-/
-- #guard_msgs in
-- #eval tower_defense #["011111", "1A   1", "111111"] {"A": [1, 2]} #[10, 10]
-- </vc-theorems>