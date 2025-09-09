-- <vc-helpers>
-- </vc-helpers>

def find_max_improvement (games : List Nat) : Nat ⊕ Unit := sorry 

theorem find_max_improvement_positive (games : List Nat) :
  let result := find_max_improvement games
  ∀ imp, result = .inl imp → imp > 0 := sorry

theorem find_max_improvement_bounded (games : List Nat) : 
  let result := find_max_improvement games
  ∀ imp, result = .inl imp → 
    (∃ max min : Nat, games.elem max ∧ games.elem min ∧ imp ≤ max - min) := sorry

theorem find_max_improvement_exists (games : List Nat) :
  let result := find_max_improvement games
  ∀ imp, result = .inl imp →
    ∃ i j, i < j ∧ j < games.length ∧ games[i]! < games[j]! := sorry

theorem find_max_improvement_unfit (games : List Nat) :
  let result := find_max_improvement games
  result = .inr () →
    ∀ i j, i < j → j < games.length → games[j]! ≤ games[i]! := sorry

theorem find_max_improvement_monotonic (games : List Nat) :
  let result := find_max_improvement games 
  ∀ n, n ≤ games.length →
    let subresult := find_max_improvement (games.take n)
    ∀ imp subImp,
      result = .inl imp → 
      subresult = .inl subImp →
      subImp ≤ imp := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_improvement [3, 7, 1, 4, 2, 4]

/-
info: 'UNFIT'
-/
-- #guard_msgs in
-- #eval find_max_improvement [5, 4, 3, 2, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_improvement [4, 3, 2, 2, 3]

-- Apps difficulty: interview
-- Assurance level: unguarded