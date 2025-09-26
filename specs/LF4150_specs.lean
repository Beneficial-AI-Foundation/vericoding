-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_spaceship (astromap : String) : String ⊕ (Nat × Nat) := sorry

theorem find_spaceship_returns_valid_coordinates_or_lost 
  (astromap : String) : 
  match find_spaceship astromap with
  | Sum.inl msg => msg = "Spaceship lost forever." ∧ ¬(astromap.contains 'X')
  | Sum.inr (x, y) => 
    -- coordinates are within bounds
    let lines := astromap.splitOn "\n"
    x < lines.head!.length ∧
    y < lines.length 
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_spaceship_with_single_x_dimensions
  (width height : Nat)
  (h1 : width > 0)
  (h2 : height > 0) :
  find_spaceship (String.intercalate "\n" ((List.replicate (height-1) (String.mk (List.replicate width '.'))) ++ 
                [String.mk (List.replicate (width/2) '.') ++ "X" ++ 
                 String.mk (List.replicate (width - width/2 - 1) '.')])) 
  = Sum.inr (width/2, 0) := sorry

theorem find_spaceship_empty_map :
  find_spaceship "" = Sum.inl "Spaceship lost forever." := sorry

theorem find_spaceship_single_dot :
  find_spaceship "." = Sum.inl "Spaceship lost forever." := sorry

theorem find_spaceship_single_x :
  find_spaceship "X" = Sum.inr (0, 0) := sorry
-- </vc-theorems>