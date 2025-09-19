-- <vc-preamble>
def list_max (l : List Int) : Int :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs

def list_unique (l : List Int) : Prop :=
  ∀ (i j : Fin l.length), i.val ≠ j.val → l[i] ≠ l[j]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_qualified_teams (n : Nat) (k : Nat) (scores : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_qualified_teams_bounds (n : Nat) (k : Nat) (scores : List Int)
    (h1 : k > 0)
    (h2 : k ≤ scores.length)
    (h3 : scores.length = n) :
    k ≤ count_qualified_teams n k scores ∧ count_qualified_teams n k scores ≤ n :=
sorry

theorem count_qualified_teams_deterministic (n : Nat) (k : Nat) (scores : List Int)
    (h1 : k > 0)
    (h2 : k ≤ scores.length)
    (h3 : scores.length = n) :
    count_qualified_teams n k scores = count_qualified_teams n k scores :=
sorry
-- </vc-theorems>