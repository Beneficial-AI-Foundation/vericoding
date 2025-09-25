-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + xs.sum

instance : LE Problem where
  le a b := a.difficulty ≤ b.difficulty

def List.sorted [Ord α] (l : List α) : List α :=
  l.toArray.qsort (fun x y => compare x y == .lt) |>.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_contest (n : Nat) (train_efficiency : Float) (time_limit : Float) (problems : List Problem) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_contest_non_negative 
  {n : Nat} {train_efficiency : Float} {time_limit : Float} {problems : List Problem}
  (h1 : train_efficiency ≥ 0.1) (h2 : train_efficiency ≤ 10) 
  (h3 : time_limit ≥ 1) (h4 : time_limit ≤ 100)
  (h5 : problems.length = n) (h6 : n ≥ 1) (h7 : n ≤ 10) :
  solve_contest n train_efficiency time_limit problems ≥ 0 := 
sorry

theorem solve_contest_upper_bound
  {n : Nat} {train_efficiency : Float} {time_limit : Float} {problems : List Problem}
  (h1 : train_efficiency ≥ 0.1) (h2 : train_efficiency ≤ 10)
  (h3 : time_limit ≥ 1) (h4 : time_limit ≤ 100)
  (h5 : problems.length = n) (h6 : n ≥ 1) (h7 : n ≤ 10) :
  solve_contest n train_efficiency time_limit problems ≤ Float.ofNat ((problems.map Problem.score).sum) := 
sorry

theorem solve_contest_time_monotonic
  {n : Nat} {train_efficiency : Float} {time_limit high_time : Float} {problems : List Problem}
  (h1 : train_efficiency ≥ 0.1) (h2 : train_efficiency ≤ 10)
  (h3 : high_time > 1000) (h4 : time_limit = high_time / 10)
  (h5 : problems.length = n) (h6 : n ≥ 1) (h7 : n ≤ 10) :
  solve_contest n train_efficiency high_time problems ≥ solve_contest n train_efficiency time_limit problems :=
sorry

theorem problem_sorting_property
  {problems : List Problem} (h1 : problems.length ≥ 1) (h2 : problems.length ≤ 10) :
  let sorted := problems.sorted
  ∀ i, i + 1 < sorted.length → 
    (sorted.get! i).difficulty ≥ (sorted.get! (i + 1)).difficulty := 
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_contest 4 1.0 31.0 #[Problem(12, 3), Problem(20, 6), Problem(30, 1), Problem(5, 1)]

/-
info: 20
-/
-- #guard_msgs in
-- #eval solve_contest 3 1.0 30.0 #[Problem(1, 10), Problem(10, 10), Problem(20, 8)]
-- </vc-theorems>