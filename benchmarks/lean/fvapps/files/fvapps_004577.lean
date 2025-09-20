-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f : List (List Int) → List (List Int) :=
sorry

def g : List (List Int) → List (List Int) :=
sorry

def perform : String → String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem f_g_inverse {matrix : List (List Int)} (h1 : matrix.length > 0)
  (h2 : ∀ row ∈ matrix, row.length > 0)
  (h3 : ∀ row ∈ matrix, row.length = matrix.head!.length) :
  f (g matrix) = matrix :=
sorry

theorem perform_maintains_valid_colors (sequence : String) :
  ∀ c, c.toString ∈ (perform sequence).data.map toString →
  c = 'y' ∨ c = 'g' ∨ c = 'b' ∨ c = 'o' ∨ c = 'r' ∨ c = 'w' :=
sorry

theorem perform_F_move :
  perform "F" = "yyyyybbbbbbrbbrbbrrrrrrrrrrgggggggggooooooooowwwwwwwww" :=
sorry

theorem perform_F2_move :
  perform "F2" = "yyyyyywwwbbgbbgbbgrrrrrrrrrbggbggbggoooooooooyyywwwwww" :=
sorry

theorem perform_F_prime_move :
  perform "F'" = "yyyyyooobbwbbwbbwrrrrrrrrrwggwggwggooooooooobbbrwwwww" :=
sorry
-- </vc-theorems>