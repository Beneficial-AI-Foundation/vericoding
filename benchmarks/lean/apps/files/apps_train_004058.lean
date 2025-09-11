-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tankvol (h : Float) (d : Float) (vt : Int) : Int := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tankvol_output_is_bounded 
  (h d : Float) (vt : Int) 
  (h_pos : h ≥ 0.1)
  (d_pos : d ≥ 0.1) 
  (d_bound : d ≤ 1000)
  (h_bound : h ≤ d)
  (vt_pos : vt ≥ 1)
  (vt_bound : vt ≤ 1000000) :
  0 ≤ tankvol h d vt ∧ tankvol h d vt ≤ vt := sorry

theorem tankvol_full_height
  (d : Float) (vt : Int)
  (d_pos : d ≥ 0.1)
  (d_bound : d ≤ 1000)
  (vt_pos : vt ≥ 1)  
  (vt_bound : vt ≤ 1000000) :
  tankvol d d vt = vt := sorry

theorem tankvol_half_height
  (d : Float) (vt : Int)
  (d_pos : d ≥ 0.1)
  (d_bound : d ≤ 1000)
  (vt_pos : vt ≥ 1)
  (vt_bound : vt ≤ 1000000) :
  tankvol (d/2) d vt = vt/2 := sorry

theorem tankvol_empty
  (d : Float) (vt : Int)
  (d_pos : d ≥ 0.1)
  (d_bound : d ≤ 1000)
  (vt_pos : vt ≥ 1)
  (vt_bound : vt ≤ 1000000) :
  tankvol 0 d vt = 0 := sorry

/-
info: 1021
-/
-- #guard_msgs in
-- #eval tankvol 40 120 3500

/-
info: 1750
-/
-- #guard_msgs in
-- #eval tankvol 60 120 3500

/-
info: 2478
-/
-- #guard_msgs in
-- #eval tankvol 80 120 3500
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded