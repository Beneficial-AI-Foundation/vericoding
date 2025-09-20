-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ant_bridge (ants : String) (terrain : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ant_bridge_length_preservation
    (ants : String) (terrain : String) :
    (ant_bridge ants terrain).length = ants.length :=
  sorry

theorem ant_bridge_character_preservation
    (ants : String) (terrain : String) :
    (ant_bridge ants terrain).data.toArray.qsort (· < ·) = ants.data.toArray.qsort (· < ·) :=
  sorry

theorem ant_bridge_is_rotation
    (ants : String) (terrain : String) :
    ∃ i : Nat, i < ants.length ∧
    ant_bridge ants terrain = 
      (String.mk (ants.data.drop i) ++ String.mk (ants.data.take i)) :=
  sorry

theorem ant_bridge_no_gaps
    (ants : String) (n : Nat) :
    ant_bridge ants (String.mk (List.replicate n '-')) = ants :=
  sorry
-- </vc-theorems>