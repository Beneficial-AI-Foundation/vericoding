/-
Late last night in the Tanner household, ALF was repairing his spaceship so he might get back to Melmac. Unfortunately for him, he forgot to put on the parking brake, and the spaceship took off during repair. Now it's hovering in space.

ALF has the technology to bring the spaceship home if he can lock on to its location.

Given a map:

````
..........
..........
..........
.......X..
..........
..........
````

The map will be given in the form of a string with \n separating new lines. The bottom left of the map is [0, 0]. X is ALF's spaceship.

In this example:

If you cannot find the spaceship, the result should be

```
"Spaceship lost forever."
```

Can you help ALF?

Check out my other 80's Kids Katas:

80's Kids #1: How Many Licks Does It Take
80's Kids #2: Help Alf Find His Spaceship
80's Kids #3: Punky Brewster's Socks
80's Kids #4: Legends of the Hidden Temple
80's Kids #5: You Can't Do That on Television
80's Kids #6: Rock 'Em, Sock 'Em Robots
80's Kids #7: She's a Small Wonder
80's Kids #8: The Secret World of Alex Mack
80's Kids #9: Down in Fraggle Rock 
80's Kids #10: Captain Planet
-/

-- <vc-helpers>
-- </vc-helpers>

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

/-
info: [7, 2]
-/
-- #guard_msgs in
-- #eval find_spaceship "..........\n..........\n.......X..\n..........\n.........."

/-
info: [0, 0]
-/
-- #guard_msgs in
-- #eval find_spaceship ".......\nX......."

/-
info: 'Spaceship lost forever.'
-/
-- #guard_msgs in
-- #eval find_spaceship "........................"

-- Apps difficulty: introductory
-- Assurance level: unguarded