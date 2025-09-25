-- <vc-preamble>
def minFlips (mat: Matrix) : Int :=
  sorry

def isZeroMatrix (m: Matrix) : Bool :=
  match m with
  | Matrix.mk rows => rows.all (fun row => row.all (fun x => x = 0))

def flipCells (mat: Matrix) (state: Nat) : Matrix :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isOnesMatrix (m: Matrix) : Bool := 
  match m with
  | Matrix.mk rows => rows.all (fun row => row.all (fun x => x = 1))
-- </vc-definitions>

-- <vc-theorems>
theorem minflips_result_valid (mat: Matrix) : 
  minFlips mat ≥ -1 :=
  sorry

theorem minflips_zero_matrix (mat: Matrix)
  (h: isZeroMatrix mat = true) :
  minFlips mat = 0 :=
  sorry

theorem minflips_minus_one_means_impossible (mat: Matrix)
  (h: minFlips mat = -1) :
  ∀ state, ¬ isZeroMatrix (flipCells mat state) :=
  sorry

theorem minflips_ones_matrix_valid (mat: Matrix)
  (h: isOnesMatrix mat = true) :
  minFlips mat ≥ -1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval minFlips [[0, 0], [0, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval minFlips [[0]]

/-
info: 6
-/
-- #guard_msgs in
-- #eval minFlips [[1, 1, 1], [1, 0, 1], [0, 0, 0]]
-- </vc-theorems>