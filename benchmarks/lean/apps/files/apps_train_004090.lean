def chessBishopDream (boardSize: List Int) (initPos: List Int) (initDir: List Int) (k: Nat) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def inRange (x: Int) (lower: Int) (upper: Int) : Prop :=
  lower ≤ x ∧ x < upper

theorem bishop_within_boundaries
  (boardSize: List Int)
  (initPos: List Int) 
  (initDir: List Int)
  (k: Nat)
  (h1: boardSize.length = 2)
  (h2: initPos.length = 2)
  (h3: initDir.length = 2)
  (h4: ∀ x ∈ boardSize, 1 ≤ x ∧ x ≤ 100)
  (h5: ∀ x ∈ initPos, 0 ≤ x ∧ x ≤ 100)
  (h6: ∀ x ∈ initDir, x = -1 ∨ x = 1)
  (h7: 0 ≤ k ∧ k ≤ 1000) :
  let result := chessBishopDream boardSize initPos initDir k
  List.length result = 2 ∧
  (∀ i < 2, inRange (result[i]!) 0 (boardSize[i]!)) :=
sorry

theorem bishop_periodic
  (boardSize: List Int)
  (initPos: List Int)
  (initDir: List Int)
  (h1: boardSize.length = 2)
  (h2: initPos.length = 2)
  (h3: initDir.length = 2)
  (h4: ∀ x ∈ boardSize, 1 ≤ x ∧ x ≤ 100)
  (h5: ∀ x ∈ initPos, 0 ≤ x ∧ x ≤ 100)
  (h6: ∀ x ∈ initDir, x = -1 ∨ x = 1) :
  let period := (4 * boardSize[0]! * boardSize[1]!).toNat
  chessBishopDream boardSize initPos initDir period = 
  chessBishopDream boardSize initPos initDir 0 :=
sorry

theorem bishop_reflection
  (boardSize: List Int)
  (initPos: List Int)
  (initDir: List Int)
  (k: Nat)
  (h1: boardSize.length = 2)
  (h2: initPos.length = 2)
  (h3: initDir.length = 2)
  (h4: ∀ x ∈ boardSize, 1 ≤ x ∧ x ≤ 100)
  (h5: ∀ x ∈ initPos, 0 ≤ x ∧ x ≤ 100)
  (h6: ∀ x ∈ initDir, x = -1 ∨ x = 1)
  (h7: 0 ≤ k ∧ k ≤ 1000) :
  let result := chessBishopDream boardSize initPos initDir k
  List.length result = 2 ∧
  (∀ i < 2, result[i]! ≤ boardSize[i]!) :=
sorry

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval chess_bishop_dream [3, 7] [1, 2] [-1, 1] 13

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval chess_bishop_dream [1, 2] [0, 0] [1, 1] 6

/-
info: [1, 0]
-/
-- #guard_msgs in
-- #eval chess_bishop_dream [2, 2] [1, 0] [1, 1] 12

-- Apps difficulty: introductory
-- Assurance level: unguarded