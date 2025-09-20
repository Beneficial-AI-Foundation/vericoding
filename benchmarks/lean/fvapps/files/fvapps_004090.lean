-- <vc-preamble>
def inRange (x: Int) (lower: Int) (upper: Int) : Prop :=
  lower ≤ x ∧ x < upper
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chessBishopDream (boardSize: List Int) (initPos: List Int) (initDir: List Int) (k: Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>