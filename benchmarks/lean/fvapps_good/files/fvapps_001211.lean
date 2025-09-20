-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_balanced_contest (n : Nat) (p : Nat) (solved_counts : List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_balanced_contest_valid_output (n : Nat) (p : Nat) (solved_counts : List Nat) 
    (h1 : p ≥ 10) (h2 : p ≤ 10000) (h3 : solved_counts.length ≥ 3) (h4 : solved_counts.length ≤ 1000) :
  let result := is_balanced_contest n p solved_counts
  result = "yes" ∨ result = "no" :=
sorry

theorem is_balanced_contest_yes_conditions (n : Nat) (p : Nat) (solved_counts : List Nat)
    (h1 : p ≥ 10) (h2 : p ≤ 10000) (h3 : solved_counts.length ≥ 3) (h4 : solved_counts.length ≤ 1000)
    (h5 : is_balanced_contest n p solved_counts = "yes") :
  let cakewalk := solved_counts.filter (fun x => x ≥ p/2)
  let hard := solved_counts.filter (fun x => x ≤ p/10)
  cakewalk.length = 1 ∧ hard.length = 2 :=
sorry

theorem is_balanced_contest_all_same (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/4, p/4, p/4] = "no" :=
sorry

theorem is_balanced_contest_no_hard (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/2, p/2, p/2] = "no" :=
sorry

theorem is_balanced_contest_no_cakewalk (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/10, p/10, p/10] = "no" :=
sorry

theorem is_balanced_contest_perfect_case (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/10, p/10, p/2] = "yes" :=
sorry
-- </vc-theorems>