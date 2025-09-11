-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_poker (john: String) (uncle: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_poker_idempotent 
  (john: String) (uncle: String) :
  uncle = "S2D2H2C2" →
  sort_poker (sort_poker john uncle) uncle = sort_poker john uncle :=
sorry

/-
info: 'S3SJSKSAH2H5H10C5C7CQD2D5D6'
-/
-- #guard_msgs in
-- #eval sort_poker "D6H2S3D5SJCQSKC7D2C5H5H10SA" "S2S3S5HJHQHKC8C9C10D4D5D6D7"

/-
info: 'C5C7CQD2D5D6S3SJSKSAH2H5H10'
-/
-- #guard_msgs in
-- #eval sort_poker "D6H2S3D5SJCQSKC7D2C5H5H10SA" "C8C9C10D4D5D6D7S2S3S5HJHQHK"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded