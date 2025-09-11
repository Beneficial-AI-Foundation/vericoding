-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tripleShiftian (T : List Int) (n : Nat) : Int := sorry

theorem tripleShiftian_first_three_elements {T : List Int} (h : T.length = 3) (i : Nat) (h' : i < 3) : 
  tripleShiftian T i = T.get ⟨i, by sorry⟩ := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tripleShiftian_recurrence {T : List Int} (h : T.length = 3) (n : Nat) (h' : n ≥ 3) :
  tripleShiftian T n = 
    4 * tripleShiftian T (n-1) - 
    5 * tripleShiftian T (n-2) + 
    3 * tripleShiftian T (n-3) := sorry

structure Matrix (m n : Nat) where
  data : Array (Array Int)

theorem tripleShiftian_matrix_formula {T : List Int} (h : T.length = 3) (n : Nat) :
  ∃ A : Matrix 3 3,
  ∃ x₀ : Matrix 3 1,
    tripleShiftian T n = 
      if n < 3 
      then T.get ⟨n, by sorry⟩  
      else sorry := sorry

/-
info: 1219856746
-/
-- #guard_msgs in
-- #eval triple_shiftian #[1, 1, 1] 25

/-
info: 2052198929
-/
-- #guard_msgs in
-- #eval triple_shiftian #[1, 2, 3] 25

/-
info: 2
-/
-- #guard_msgs in
-- #eval triple_shiftian #[6, 7, 2] 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded