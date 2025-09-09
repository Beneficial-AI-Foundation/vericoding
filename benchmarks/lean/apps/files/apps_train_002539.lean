def validColors := ["red", "yellow", "green"]
def validTextures := ["smooth", "bumpy"]

-- <vc-helpers>
-- </vc-helpers>

def colorProbability (color: String) (texture: String) : Float :=
  sorry

theorem probability_in_bounds (color: String) (texture: String)
  (h1: color ∈ validColors) (h2: texture ∈ validTextures) :
  let p := colorProbability color texture
  0 ≤ p ∧ p ≤ 1 :=
sorry

theorem invalid_color_error (color: String) (texture: String)
  (h: color ∉ validColors) (h2: texture ∈ validTextures) :
  (colorProbability color texture).isNaN :=
sorry

theorem invalid_texture_error (color: String) (texture: String)
  (h1: color ∈ validColors) (h: texture ∉ validTextures) :
  (colorProbability color texture).isNaN :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded