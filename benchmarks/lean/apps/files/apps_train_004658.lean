-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def martingale (bank : Float) (outcomes : List Int) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem martingale_monotonic_bank {bank : Float} {outcomes : List Int} :
  ∀ inc : Float, inc ≥ 0 → martingale (bank + inc) outcomes ≥ martingale bank outcomes := by
  sorry

theorem martingale_all_wins {bank : Float} {outcomes : List Int} :
  (∀ x ∈ outcomes, x = 1) → 
  martingale bank outcomes = bank + (outcomes.length.toFloat * 100) := by
  sorry

theorem martingale_empty_outcomes {bank : Float} :
  martingale bank [] = bank := by
  sorry

theorem martingale_returns_float {bank : Float} {outcomes : List Int} :
  ∃ x : Float, martingale bank outcomes = x := by
  sorry

theorem martingale_consecutive_losses {n : Nat} :
  let losses := List.replicate n 0
  martingale 0 losses = -(List.range n).foldl (fun acc i => acc + 100 * (Float.pow 2 i.toFloat)) 0 := by
  sorry

/-
info: 1300
-/
-- #guard_msgs in
-- #eval martingale 1000 [1, 1, 0, 0, 1]

/-
info: 800
-/
-- #guard_msgs in
-- #eval martingale 500 [1, 1, 1]

/-
info: -600
-/
-- #guard_msgs in
-- #eval martingale 100 [0, 0, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded