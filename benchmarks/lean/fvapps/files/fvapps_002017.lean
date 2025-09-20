-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_killer_pairs (initial : String × String) (murders : List (String × String)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_killer_pairs_result_type 
  (initial : String × String) 
  (murders : List (String × String)) :
  ∀ x ∈ solve_killer_pairs initial murders, x.data.all Char.isAlpha :=
  sorry

theorem solve_killer_pairs_result_length
  (initial : String × String)
  (murders : List (String × String)) :
  (solve_killer_pairs initial murders).length = murders.length + 1 :=
  sorry

theorem solve_killer_pairs_initial_state
  (initial : String × String)
  (murders : List (String × String)) :
  (solve_killer_pairs initial murders).head! = s!"{initial.1} {initial.2}" :=
  sorry

theorem solve_killer_pairs_space_format
  (initial : String × String)
  (murders : List (String × String)) :
  ∀ x ∈ solve_killer_pairs initial murders,
  (x.split (· = ' ')).length = 2 :=
  sorry

theorem solve_killer_pairs_state_transitions
  (initial : String × String)
  (murders : List (String × String)) :
  ∀ i < murders.length,
  let current := murders.take i |>.foldl 
    (λ acc (m : String × String) => 
      if acc.1 = m.1 
      then (m.2, acc.2)
      else (acc.1, m.2)) 
    initial
  (solve_killer_pairs initial murders)[i+1]! = s!"{current.1} {current.2}" :=
  sorry
-- </vc-theorems>