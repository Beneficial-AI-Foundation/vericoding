-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def goals (laliga : Int) (copa : Int) (champions : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>