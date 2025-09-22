-- <vc-preamble>

def ValidInput (n m x y : Int) (xx yy : List Int) : Prop :=
  xx.length = n ∧ yy.length = m ∧ n ≥ 1 ∧ m ≥ 1 ∧ x < y

def AgreementPossible (n m x y : Int) (xx yy : List Int) (h_valid : ValidInput n m x y xx yy) : Prop :=
  let combined_x := xx ++ [x]
  let combined_y := yy ++ [y]
  (∃ max_val, max_val ∈ combined_x ∧ 
              (∀ v, v ∈ combined_x → v ≤ max_val) ∧
   ∃ min_val, min_val ∈ combined_y ∧ 
              (∀ v, v ∈ combined_y → v ≥ min_val) ∧
              max_val < min_val)

@[reducible, simp]
def solve_precond (n m x y : Int) (xx yy : List Int) : Prop :=
  ValidInput n m x y xx yy
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m x y : Int) (xx yy : List Int) (h_precond : solve_precond n m x y xx yy) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m x y : Int) (xx yy : List Int) (result: String) (h_precond : solve_precond n m x y xx yy) : Prop :=
  (result = "No War" ∨ result = "War") ∧
  (result = "No War" ↔ AgreementPossible n m x y xx yy h_precond)

theorem solve_spec_satisfied (n m x y : Int) (xx yy : List Int) (h_precond : solve_precond n m x y xx yy) :
    solve_postcond n m x y xx yy (solve n m x y xx yy h_precond) h_precond := by
  sorry
-- </vc-theorems>