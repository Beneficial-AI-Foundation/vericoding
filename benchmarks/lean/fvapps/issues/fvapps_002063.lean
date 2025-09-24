-- <vc-preamble>
def colorRectangles (rectangles : List (Int × Int × Int × Int)) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parseColors (s : String) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem colorRectangles_valid_format (rectangles : List (Int × Int × Int × Int)) :
  let result := colorRectangles rectangles
  result.startsWith "YES\n" := by sorry

theorem colorRectangles_output_length {rectangles : List (Int × Int × Int × Int)} :
  let colors := parseColors (colorRectangles rectangles)
  colors.length = rectangles.length := by sorry

theorem colorRectangles_valid_colors {rectangles : List (Int × Int × Int × Int)} :
  let colors := parseColors (colorRectangles rectangles)
  ∀ c ∈ colors, 1 ≤ c ∧ c ≤ 4 := by sorry

theorem colorRectangles_parity_color_assignment 
  {rectangles : List (Int × Int × Int × Int)} :
  let colors := parseColors (colorRectangles rectangles)
  ∀ (rect : Int × Int × Int × Int) (color : Int),
    rect ∈ rectangles →
    color ∈ colors →
    (Int.mod (Prod.fst rect) 2 = 0 ∧ Int.mod (Prod.fst (Prod.snd rect)) 2 = 0 → color = 1) ∧
    (Int.mod (Prod.fst rect) 2 = 0 ∧ Int.mod (Prod.fst (Prod.snd rect)) 2 ≠ 0 → color = 2) ∧
    (Int.mod (Prod.fst rect) 2 ≠ 0 ∧ Int.mod (Prod.fst (Prod.snd rect)) 2 = 0 → color = 3) ∧
    (Int.mod (Prod.fst rect) 2 ≠ 0 ∧ Int.mod (Prod.fst (Prod.snd rect)) 2 ≠ 0 → color = 4) := by sorry
-- </vc-theorems>