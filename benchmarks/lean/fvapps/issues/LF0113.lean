-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_max_damage (spells : List Spell) : List Int := sorry

theorem length_preservation (spells : List Spell) :
  List.length (calculate_max_damage spells) = List.length spells := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_are_ints (spells : List Spell) (i : Nat) (h : i < List.length spells) :
  ∃ n : Int, (calculate_max_damage spells).get ⟨i, by rw [length_preservation]; exact h⟩ = n := sorry

theorem type0_positive_running_sum (spells : List Spell) 
  (h_type : ∀ s ∈ spells, s.spellType = 0)
  (h_damage : ∀ s ∈ spells, s.damage > 0) 
  (i : Nat) (h : i < List.length spells) :
  (calculate_max_damage spells).get ⟨i, by rw [length_preservation]; exact h⟩ = 
  (spells.take (i+1)).foldl (fun acc s => acc + s.damage) 0 := sorry
-- </vc-theorems>