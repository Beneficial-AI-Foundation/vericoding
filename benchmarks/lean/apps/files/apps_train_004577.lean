def f : List (List Int) → List (List Int) := sorry
def g : List (List Int) → List (List Int) := sorry

-- <vc-helpers>
-- </vc-helpers>

def perform : String → String := sorry 

theorem f_g_inverse {matrix : List (List Int)} (h1 : matrix.length > 0) 
  (h2 : ∀ row ∈ matrix, row.length > 0)
  (h3 : ∀ row ∈ matrix, row.length = matrix.head!.length) :
  f (g matrix) = matrix := sorry

theorem perform_maintains_valid_colors (sequence : String) :
  ∀ c, c.toString ∈ (perform sequence).data.map toString → 
  c = 'y' ∨ c = 'g' ∨ c = 'b' ∨ c = 'o' ∨ c = 'r' ∨ c = 'w' := sorry

theorem perform_F_move :
  perform "F" = "yyyyybbbbbbrbbrbbrrrrrrrrrrgggggggggooooooooowwwwwwwww" := sorry

theorem perform_F2_move :
  perform "F2" = "yyyyyywwwbbgbbgbbgrrrrrrrrrbggbggbggoooooooooyyywwwwww" := sorry

theorem perform_F_prime_move :
  perform "F'" = "yyyyyooobbwbbwbbwrrrrrrrrrwggwggwggooooooooobbbrwwwww" := sorry

/-
info: 'yyyyybbbbbbrbbrbbrrrrrrrrrrgggggggggooooooooowwwwwwwww'
-/
-- #guard_msgs in
-- #eval perform "F"

/-
info: 'yyyyyywwwbbgbbgbbgrrrrrrrrrbggbggbggoooooooooyyywwwwww'
-/
-- #guard_msgs in
-- #eval perform "F2"

/-
info: 'yyyyyooobbwbbwbbwrrrrrrrrrwggwggwggooooooooobbbrwwwww'
-/
-- #guard_msgs in
-- #eval perform "F""

-- Apps difficulty: introductory
-- Assurance level: unguarded