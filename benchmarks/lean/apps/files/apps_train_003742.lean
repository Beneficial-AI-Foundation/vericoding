-- <vc-helpers>
-- </vc-helpers>

def ellipse (a b : Float) : String := sorry

theorem ellipse_format_valid (a b : Float)
  (h1 : a > 1)
  (h2 : b > 1) :
  let result := ellipse a b
  ∃ area perim : Float,
  area > 0 ∧ 
  perim > 0 ∧
  (result.any fun c => c = 'A') ∧ 
  (result.any fun c => c = 'p') := sorry

theorem ellipse_circle_case (r : Float)
  (h : r > 1) :
  let result := ellipse r r
  ∃ perim : Float,
  let expected := 2 * (3.14159 : Float) * r
  (perim - expected).abs ≤ 0.2 * expected := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded