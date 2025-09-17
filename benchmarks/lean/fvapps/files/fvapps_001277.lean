-- <vc-preamble>
def count_qualified_teams (n : Nat) (k : Nat) (scores : List Int) : Nat := sorry

theorem count_qualified_teams_bounds (n : Nat) (k : Nat) (scores : List Int) 
    (h1 : k > 0)
    (h2 : k ≤ scores.length)
    (h3 : scores.length = n) :
    k ≤ count_qualified_teams n k scores ∧ count_qualified_teams n k scores ≤ n := sorry

def list_max (l : List Int) : Int := 
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_unique (l : List Int) : Prop :=
  ∀ (i j : Fin l.length), i.val ≠ j.val → l[i] ≠ l[j]
-- </vc-definitions>

-- <vc-theorems>
theorem count_qualified_teams_deterministic (n : Nat) (k : Nat) (scores : List Int)
    (h1 : k > 0)
    (h2 : k ≤ scores.length)
    (h3 : scores.length = n) :
    count_qualified_teams n k scores = count_qualified_teams n k scores := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_qualified_teams 5 1 [3, 5, 2, 4, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_qualified_teams 6 4 [6, 5, 4, 3, 2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_qualified_teams 4 2 [10, 10, 8, 8]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible