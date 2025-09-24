-- <vc-preamble>
def lemming_battle (battlefield : Nat) (green blue : List Nat) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse_survivors (s : String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lemming_battle_valid_result (battlefield : Nat) (green blue : List Nat)
    (h1 : battlefield > 0) (h2 : battlefield ≤ 100)
    (h3 : ∀ x ∈ green, x > 0 ∧ x ≤ 1000) 
    (h4 : ∀ x ∈ blue, x > 0 ∧ x ≤ 1000)
    (h5 : green ≠ []) (h6 : blue ≠ []) :
    let result := lemming_battle battlefield green blue
    (result = "Green and Blue died" ∨ 
     (∃ s : String, result = "Green wins: " ++ s) ∨
     (∃ s : String, result = "Blue wins: " ++ s)) := sorry

theorem lemming_battle_survivor_count (battlefield : Nat) (green blue : List Nat)
    (h1 : battlefield > 0) (h2 : battlefield ≤ 100)
    (h3 : ∀ x ∈ green, x > 0 ∧ x ≤ 1000)
    (h4 : ∀ x ∈ blue, x > 0 ∧ x ≤ 1000)
    (h5 : green ≠ []) (h6 : blue ≠ []) :
    let result := lemming_battle battlefield green blue 
    ((result.startsWith "Green wins" → List.length (parse_survivors result) ≤ List.length green) ∧
     (result.startsWith "Blue wins" → List.length (parse_survivors result) ≤ List.length blue)) := sorry

theorem lemming_battle_max_survivor_value (battlefield : Nat) (green blue : List Nat)
    (h1 : battlefield > 0) (h2 : battlefield ≤ 100)
    (h3 : ∀ x ∈ green, x > 0 ∧ x ≤ 1000)
    (h4 : ∀ x ∈ blue, x > 0 ∧ x ≤ 1000)
    (h5 : green ≠ []) (h6 : blue ≠ []) :
    let result := lemming_battle battlefield green blue
    let maxGreen := (List.maximum? green).getD 0
    let maxBlue := (List.maximum? blue).getD 0
    ∀ s ∈ parse_survivors result, s ≤ max maxGreen maxBlue := sorry

theorem equal_armies_draw (n : Nat) 
    (h1 : n > 0) (h2 : n ≤ 100) :
    lemming_battle 1 [n] [n] = "Green and Blue died" := sorry

theorem battlefield_size_limit (battlefield army_size : Nat)
    (h1 : battlefield > 0) (h2 : battlefield ≤ 100)
    (h3 : army_size > 0) (h4 : army_size ≤ 100) :
    lemming_battle battlefield (List.replicate army_size 1) (List.replicate army_size 1) = "Green and Blue died" := sorry

/-
info: 'Green and Blue died'
-/
-- #guard_msgs in
-- #eval lemming_battle 5 [10] [10]

/-
info: 'Blue wins: 5'
-/
-- #guard_msgs in
-- #eval lemming_battle 2 [20, 10] [10, 10, 15]

/-
info: 'Green wins: 10 10'
-/
-- #guard_msgs in
-- #eval lemming_battle 3 [50, 40, 30, 40, 50] [50, 30, 30, 20, 60]
-- </vc-theorems>