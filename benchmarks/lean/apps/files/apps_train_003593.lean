-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Char.isAscii (c : Char) : Bool := sorry

def siegfried (week : Nat) (text : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem siegfried_length (week : Nat) (text : String) 
  (h1 : week ≤ 5) (h2 : text.length > 0) : 
  (siegfried week text).length ≤ text.length := sorry

theorem siegfried_consistent (text : String) (h : text.length > 0) :
  siegfried 5 text = siegfried 5 text := sorry

theorem siegfried_idempotent (week : Nat) (text : String) 
  (h1 : week ≤ 5) (h2 : text.length > 0) :
  siegfried week (siegfried week text) = siegfried week text := sorry

theorem siegfried_week_0 (text : String) (h : text.length > 0) :
  siegfried 0 text = text := sorry

theorem siegfried_c_replacement (text : String) 
  (h1 : text.length > 0)
  (h2 : ∀ c ∈ text.data, c = 'c' ∨ c = 'C') :
  let result := siegfried 1 text
  (∀ c ∈ result.data, c.toLower ≠ 'c') ∧
  (∃ c ∈ result.data, c.toLower = 'k') := sorry

/-
info: 'Sity sivilians'
-/
-- #guard_msgs in
-- #eval siegfried 1 "City civilians"

/-
info: 'Met me at the sam plas at non'
-/
-- #guard_msgs in
-- #eval siegfried 3 "Meet me at the same place at noon"

/-
info: 'Schmart und 99 ver husbund und vif'
-/
-- #guard_msgs in
-- #eval siegfried 5 "Smart and 99 were husband and wife"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded