-- <vc-preamble>
inductive Result where
  | Impossible : Result
  | Possible : Int → List (Int × Int) → Result

def seq_sum : List Int → Int
  | [] => 0
  | h :: t => h + seq_sum t

def seq_sum_first (s : List Int) (n : Int) : Int :=
  if n ≤ 0 then 0
  else if n.natAbs > s.length then seq_sum s
  else seq_sum (s.take n.natAbs)

def min_index_helper (weights : List Int) (current_min : Nat) (next : Nat) : Nat :=
  if next ≥ weights.length then current_min
  else 
    match weights[next]?, weights[current_min]? with
    | some w1, some w2 => 
      if w1 < w2 then min_index_helper weights next (next + 1)
      else min_index_helper weights current_min (next + 1)
    | _, _ => min_index_helper weights current_min (next + 1)
termination_by weights.length - next

def min_index (weights : List Int) : Int :=
  if weights.isEmpty then 0
  else Int.ofNat (min_index_helper weights 0 1)

def min_index_excluding_helper (weights : List Int) (exclude : Int) (current_min : Nat) (next : Nat) : Nat :=
  if next ≥ weights.length then current_min
  else if Int.ofNat next = exclude then min_index_excluding_helper weights exclude current_min (next + 1)
  else 
    match weights[next]?, weights[current_min]? with
    | some w1, some w2 => 
      if w1 < w2 then min_index_excluding_helper weights exclude next (next + 1)
      else min_index_excluding_helper weights exclude current_min (next + 1)
    | _, _ => min_index_excluding_helper weights exclude current_min (next + 1)
termination_by weights.length - next

def min_index_excluding (weights : List Int) (exclude : Int) : Int :=
  let first_valid : Nat := if exclude = 0 then 1 else 0
  Int.ofNat (min_index_excluding_helper weights exclude first_valid 0)

@[reducible, simp]
def solve_precond (t : Int) (cases : List (Int × Int × List Int)) : Prop :=
  t ≥ 0 ∧ 
  cases.length = t.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < t → 
    let case := cases[i.natAbs]?
    match case with
    | some (n, m, weights) => n ≥ 0 ∧ m ≥ 0 ∧ weights.length = n.natAbs
    | none => False
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (t : Int) (cases : List (Int × Int × List Int)) (h_precond : solve_precond t cases) : List Result :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t : Int) (cases : List (Int × Int × List Int)) (results : List Result) (h_precond : solve_precond t cases) : Prop :=
  results.length = t.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < t → 
    match cases[i.natAbs]? with
    | some (n, m, _) => 
      (n ≤ 2 ∨ m < n) → 
      (match results[i.natAbs]? with | some Result.Impossible => True | _ => False)
    | none => True) ∧
  (∀ i, 0 ≤ i ∧ i < t → 
    match cases[i.natAbs]? with
    | some (n, m, _) => 
      (n > 2 ∧ m ≥ n) → 
      (match results[i.natAbs]? with 
       | some (Result.Possible _ edges) => 
         edges.length = m.natAbs ∧
         (∀ j, 0 ≤ j ∧ j < edges.length → 
           match edges[j]? with
           | some (u, v) => 1 ≤ u ∧ u ≤ n ∧ 1 ≤ v ∧ v ≤ n ∧ u ≠ v
           | none => False)
       | _ => True)
    | none => True) ∧
  (∀ i, 0 ≤ i ∧ i < t → 
    match cases[i.natAbs]? with
    | some (n, m, weights) => 
      (n > 2 ∧ m ≥ n) → 
      (match results[i.natAbs]? with 
       | some (Result.Possible cost _) => 
         let min1_idx := min_index weights
         let min2_idx := min_index_excluding weights min1_idx
         match weights[min1_idx.natAbs]?, weights[min2_idx.natAbs]? with
         | some w1, some w2 => cost = 2 * seq_sum weights + (m - n) * (w1 + w2)
         | _, _ => False
       | _ => True)
    | none => True) ∧
  (∀ i, 0 ≤ i ∧ i < t → 
    match cases[i.natAbs]? with
    | some (n, m, weights) => 
      (n > 2 ∧ m ≥ n) → 
      (match results[i.natAbs]? with 
       | some (Result.Possible _ edges) => 
         (∀ j, 0 ≤ j ∧ j < n → 
           match edges[j.natAbs]? with
           | some edge => edge = (j + 1, if j = n - 1 then 1 else j + 2)
           | none => False) ∧
         (∀ j, n ≤ j ∧ j < m → 
           let min1_idx := min_index weights
           let min2_idx := min_index_excluding weights min1_idx
           match edges[j.natAbs]? with
           | some edge => edge = (min1_idx + 1, min2_idx + 1)
           | none => False)
       | _ => True)
    | none => True)

theorem solve_spec_satisfied (t : Int) (cases : List (Int × Int × List Int)) (h_precond : solve_precond t cases) :
    solve_postcond t cases (solve t cases h_precond) h_precond := by
  sorry
-- </vc-theorems>