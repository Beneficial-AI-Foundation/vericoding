-- <vc-preamble>
def mymax (a b : Int) : Int :=
  if a ≥ b then a else b

def ValidStairs (stair_heights : List Int) : Prop :=
  stair_heights.length ≥ 1 ∧
  (∀ i, 0 ≤ i ∧ i < stair_heights.length - 1 → stair_heights[i]! ≤ stair_heights[i + 1]!) ∧
  (∀ i, 0 ≤ i ∧ i < stair_heights.length → stair_heights[i]! ≥ 0)

def ValidBoxes (boxes : List (Int × Int)) (stairs_amount : Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < boxes.length → (boxes[i]!).1 ≥ 1 ∧ (boxes[i]!).1 ≤ stairs_amount ∧ (boxes[i]!).2 ≥ 1

def ValidResult (result : List Int) (boxes : List (Int × Int)) (stair_heights : List Int) : Prop :=
  stair_heights.length ≥ 1 →
  (∀ i, 0 ≤ i ∧ i < boxes.length → (boxes[i]!).1 ≥ 1 ∧ (boxes[i]!).1 ≤ stair_heights.length) →
  result.length = boxes.length ∧
  (∀ i, 0 ≤ i ∧ i < boxes.length → result[i]! ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < boxes.length → 
      result[i]! ≥ stair_heights[0]! ∧ result[i]! ≥ stair_heights[Int.natAbs ((boxes[i]!).1 - 1)]!) ∧
  (∀ i, 0 ≤ i ∧ i < boxes.length → 
      result[i]! = mymax (if i = 0 then stair_heights[0]! else result[i-1]! + (boxes[i-1]!).2) 
                        (stair_heights[Int.natAbs ((boxes[i]!).1 - 1)]!))

@[reducible, simp]
def solve_precond (stairs_amount : Int) (stair_heights : List Int) (boxes_amount : Int) (boxes : List (Int × Int)) : Prop :=
  stairs_amount ≥ 1 ∧
  stair_heights.length = stairs_amount ∧
  boxes_amount ≥ 0 ∧
  boxes.length = boxes_amount ∧
  ValidStairs stair_heights ∧
  ValidBoxes boxes stairs_amount
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stairs_amount : Int) (stair_heights : List Int) (boxes_amount : Int) (boxes : List (Int × Int)) (h_precond : solve_precond stairs_amount stair_heights boxes_amount boxes) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stairs_amount : Int) (stair_heights : List Int) (boxes_amount : Int) (boxes : List (Int × Int)) (result : List Int) (h_precond : solve_precond stairs_amount stair_heights boxes_amount boxes) : Prop :=
  ValidResult result boxes stair_heights

theorem solve_spec_satisfied (stairs_amount : Int) (stair_heights : List Int) (boxes_amount : Int) (boxes : List (Int × Int)) (h_precond : solve_precond stairs_amount stair_heights boxes_amount boxes) :
    solve_postcond stairs_amount stair_heights boxes_amount boxes (solve stairs_amount stair_heights boxes_amount boxes h_precond) h_precond := by
  sorry
-- </vc-theorems>