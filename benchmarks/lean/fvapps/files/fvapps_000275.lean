-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSideLength (mat: List (List Int)) (threshold: Int) : Int :=
  sorry

def minElem (list: List Int) : Int :=
  sorry

def sumList (list: List Int) : Int :=
  sorry

def listSum (list: List Int) : Int :=
  sorry

def floorSqrt (n: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxSideLength_bounds {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length) :
  let result := maxSideLength mat threshold
  0 ≤ result ∧ result ≤ min mat.length mat[0]!.length :=
sorry

theorem maxSideLength_low_threshold {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : threshold < minElem (mat.map minElem)) :
  maxSideLength mat threshold = 0 :=
sorry

theorem maxSideLength_high_threshold {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : threshold ≥ listSum (mat.map sumList)) :
  maxSideLength mat threshold = min mat.length mat[0]!.length :=
sorry

theorem maxSideLength_zero_matrix {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : ∀ row ∈ mat, ∀ x ∈ row, x = 0)
  (h3 : threshold ≥ 0) :
  maxSideLength mat threshold = min mat.length mat[0]!.length :=
sorry

theorem maxSideLength_ones_matrix {mat : List (List Int)} {threshold : Int}
  (h1 : ∀ row ∈ mat, row.length = mat[0]!.length)
  (h2 : ∀ row ∈ mat, ∀ x ∈ row, x = 1) :
  maxSideLength mat threshold ≤ floorSqrt threshold :=
sorry
-- </vc-theorems>