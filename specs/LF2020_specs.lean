-- <vc-preamble>
def list_count {α} [BEq α] (p : α → Bool) (l : List α) : Nat :=
  match l with
  | [] => 0
  | x::xs => (if p x then 1 else 0) + list_count p xs

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_hacknet (n A cf cm m : Nat) (skills : List Nat) : Nat × List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_invariants {n A cf cm m : Nat} {skills ans : List Nat} {max_level : Nat}
  (h : solve_hacknet n A cf cm m skills = (max_level, ans)) :
  (ans.length = n) ∧
  (∀ x ∈ ans, x ≤ A) ∧
  (list_sum (List.map (λ i => max 0 ((ans.get! i) - (skills.get! i)))
    (List.range n)) ≤ m) ∧
  (max_level = cf * (list_count (λ x => x == A) ans) + cm * (List.foldl min A ans)) :=
sorry

theorem zero_money {n A cf : Nat} {skills : List Nat}
  (h : skills.length = n) :
  solve_hacknet n A cf 1 0 skills = (0, skills) :=
sorry

theorem infinite_money {n A : Nat} {skills : List Nat}
  (h : skills.length = n) :
  solve_hacknet n A 1 1 (Nat.max A 0) skills =
    (n + A, List.replicate n A) :=
sorry
-- </vc-theorems>