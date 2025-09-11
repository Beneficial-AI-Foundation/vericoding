-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def best_match (al_ahly: List Nat) (zamalek: List Nat) : Nat := sorry

theorem best_match_valid_index (al_ahly: List Nat) (zamalek: List Nat) 
    (h: al_ahly.length = zamalek.length) (h2: al_ahly.length > 0) :
  let result := best_match al_ahly zamalek
  0 ≤ result ∧ result < al_ahly.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem best_match_has_min_diff (al_ahly: List Nat) (zamalek: List Nat)
    (h: al_ahly.length = zamalek.length) (h2: al_ahly.length > 0) :
  let result := best_match al_ahly zamalek
  let diff := al_ahly[result]! - zamalek[result]!
  ∀ i, i < al_ahly.length → al_ahly[i]! - zamalek[i]! ≥ diff := sorry

theorem best_match_max_zamalek (al_ahly: List Nat) (zamalek: List Nat)
    (h: al_ahly.length = zamalek.length) (h2: al_ahly.length > 0) :
  let result := best_match al_ahly zamalek
  let diff := al_ahly[result]! - zamalek[result]!
  ∀ i, i < al_ahly.length → 
    al_ahly[i]! - zamalek[i]! = diff → 
    zamalek[i]! ≤ zamalek[result]! := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval best_match [6, 4] [1, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval best_match [1, 2, 3, 4, 5] [0, 1, 2, 3, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval best_match [3, 4, 3] [1, 1, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded