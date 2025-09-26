-- <vc-preamble>
def ValidInput (columns : List (Int × Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < columns.length → (columns[i]?.getD (0, 0)).1 > 0 ∧ (columns[i]?.getD (0, 0)).2 > 0

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def sum_left : List (Int × Int) → Int
  | [] => 0
  | h :: t => h.1 + sum_left t

def sum_right : List (Int × Int) → Int
  | [] => 0
  | h :: t => h.2 + sum_right t

@[reducible, simp]
def solve_precond (columns : List (Int × Int)) : Prop :=
  ValidInput columns
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (columns : List (Int × Int)) (h_precond : solve_precond columns) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (columns : List (Int × Int)) (result : Int) (h_precond : solve_precond columns) : Prop :=
  0 ≤ result ∧ result ≤ columns.length ∧
  (let L := sum_left columns
   let R := sum_right columns
   let original_beauty := abs (L - R)
   if result = 0 then
     ∀ i, 0 ≤ i ∧ i < columns.length → 
       let new_L := L - (columns[i]?.getD (0, 0)).1 + (columns[i]?.getD (0, 0)).2
       let new_R := R - (columns[i]?.getD (0, 0)).2 + (columns[i]?.getD (0, 0)).1
       abs (new_L - new_R) ≤ original_beauty
   else
     1 ≤ result ∧ result ≤ columns.length ∧
     let best_idx := Int.natAbs (result - 1)
     let best_L := L - (columns[best_idx]?.getD (0, 0)).1 + (columns[best_idx]?.getD (0, 0)).2
     let best_R := R - (columns[best_idx]?.getD (0, 0)).2 + (columns[best_idx]?.getD (0, 0)).1
     let best_beauty := abs (best_L - best_R)
     best_beauty > original_beauty ∧
     ∀ i, 0 ≤ i ∧ i < columns.length → 
       let new_L := L - (columns[i]?.getD (0, 0)).1 + (columns[i]?.getD (0, 0)).2
       let new_R := R - (columns[i]?.getD (0, 0)).2 + (columns[i]?.getD (0, 0)).1
       abs (new_L - new_R) ≤ best_beauty)

theorem solve_spec_satisfied (columns : List (Int × Int)) (h_precond : solve_precond columns) :
    solve_postcond columns (solve columns h_precond) h_precond := by
  sorry
-- </vc-theorems>