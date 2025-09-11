-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_hexagon_beam (n: Nat) (seq: List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_hexagon_beam_nonnegative {n: Nat} {seq: List Int}
  (hseq : seq.length > 0)
  (hseqnonneg : ∀ x ∈ seq, x ≥ 0) :
  max_hexagon_beam n seq ≥ 0 := sorry

/-
info: 34
-/
-- #guard_msgs in
-- #eval max_hexagon_beam 4 [2, 4, 6, 8]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_hexagon_beam 2 [1]

/-
info: 8
-/
-- #guard_msgs in
-- #eval max_hexagon_beam 3 [1, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded