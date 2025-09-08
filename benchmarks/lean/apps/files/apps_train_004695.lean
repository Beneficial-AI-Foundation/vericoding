/-
# Messi goals function

[Messi](https://en.wikipedia.org/wiki/Lionel_Messi) is a soccer player with goals in three leagues: 

- LaLiga
- Copa del Rey
- Champions

Complete the function to return his total number of goals in all three leagues.

Note: the input will always be valid.

For example:

```
5, 10, 2  -->  17
```
-/

-- <vc-helpers>
-- </vc-helpers>

def goals (laliga : Int) (copa : Int) (champions : Int) : Int :=
  sorry

theorem goals_equals_sum (laliga copa champions : Int) 
  (h1 : laliga ≥ 0) (h2 : copa ≥ 0) (h3 : champions ≥ 0) : 
  goals laliga copa champions = laliga + copa + champions :=
  sorry

theorem goals_nonnegative (laliga copa champions : Int)
  (h1 : laliga ≥ 0) (h2 : copa ≥ 0) (h3 : champions ≥ 0) :
  goals laliga copa champions ≥ 0 :=
  sorry

theorem goals_geq_laliga (laliga copa champions : Int)
  (h1 : laliga ≥ 0) (h2 : copa ≥ 0) (h3 : champions ≥ 0) :
  goals laliga copa champions ≥ laliga :=
  sorry

theorem goals_geq_copa (laliga copa champions : Int)
  (h1 : laliga ≥ 0) (h2 : copa ≥ 0) (h3 : champions ≥ 0) :
  goals laliga copa champions ≥ copa :=
  sorry

theorem goals_geq_champions (laliga copa champions : Int)
  (h1 : laliga ≥ 0) (h2 : copa ≥ 0) (h3 : champions ≥ 0) :
  goals laliga copa champions ≥ champions :=
  sorry

/-
info: 17
-/
-- #guard_msgs in
-- #eval goals 5 10 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval goals 0 0 0

/-
info: 58
-/
-- #guard_msgs in
-- #eval goals 43 10 5

-- Apps difficulty: introductory
-- Assurance level: guarded