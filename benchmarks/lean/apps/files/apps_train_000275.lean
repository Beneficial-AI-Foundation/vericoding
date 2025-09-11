-- <vc-preamble>
def maxSideLength (mat: List (List Int)) (threshold: Int) : Int :=
  sorry

def minElem (list: List Int) : Int :=
  sorry

def sumList (list: List Int) : Int :=
  sorry

def listSum (list: List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def floorSqrt (n: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxSideLength_bounds {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length) :
  let result := maxSideLength mat threshold
  0 ≤ result ∧ result ≤ min mat.length mat[0]!.length := sorry

theorem maxSideLength_low_threshold {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : threshold < minElem (mat.map minElem)) :
  maxSideLength mat threshold = 0 := sorry

theorem maxSideLength_high_threshold {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : threshold ≥ listSum (mat.map sumList)) :
  maxSideLength mat threshold = min mat.length mat[0]!.length := sorry

theorem maxSideLength_zero_matrix {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : ∀ row ∈ mat, ∀ x ∈ row, x = 0)
  (h3 : threshold ≥ 0) :
  maxSideLength mat threshold = min mat.length mat[0]!.length := sorry

theorem maxSideLength_ones_matrix {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : ∀ row ∈ mat, ∀ x ∈ row, x = 1) :
  maxSideLength mat threshold ≤ floorSqrt threshold := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxSideLength [[1, 1, 3, 2, 4, 3, 2], [1, 1, 3, 2, 4, 3, 2], [1, 1, 3, 2, 4, 3, 2]] 4

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxSideLength [[2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]] 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval maxSideLength [[1, 1, 1, 1], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]] 6
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded