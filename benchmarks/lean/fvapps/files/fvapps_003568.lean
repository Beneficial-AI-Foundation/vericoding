-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_mesh (words : List String) : String :=
sorry

def isResult (s : String) : Bool :=
sorry

def hasOverlap (s1 s2 : String) : Bool :=
sorry

def isLowerAlpha (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_mesh_output_format
  (words : List String)
  (h1 : words.length ≥ 2)
  (h2 : words.length ≤ 10)
  (h3 : ∀ w ∈ words, w.length > 0) :
  let result := word_mesh words
  (result = "failed to mesh" ∨ isLowerAlpha result) :=
sorry

theorem word_mesh_successful_overlap
  (words : List String)
  (h1 : words.length ≥ 2)
  (h2 : words.length ≤ 5)
  (h3 : ∀ w ∈ words, w.length > 0)
  (h4 : ∀ i, i < words.length - 1 →
    hasOverlap (words.get ⟨i, by sorry⟩) (words.get ⟨i+1, by sorry⟩)) :
  let result := word_mesh words
  result ≠ "failed to mesh" →
  ∀ i, i < words.length - 1 →
    hasOverlap (words.get ⟨i, by sorry⟩) (words.get ⟨i+1, by sorry⟩) :=
sorry
-- </vc-theorems>