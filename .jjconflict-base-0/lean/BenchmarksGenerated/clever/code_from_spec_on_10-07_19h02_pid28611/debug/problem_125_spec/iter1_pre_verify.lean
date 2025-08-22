import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List (List Nat) → Nat → List Nat)
(grid: List (List Nat))
(k: Nat) :=
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a.get! i < b.get! i ∧
  (∀ j, j < i → a.get! j = b.get! j));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path.get! 0 = (grid.get! i).get! j) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path.get! 1 = (grid.get! i').get! j') ∧
        ((abs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (abs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid.get! i).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid.get! i).get! j) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
∃ result, implementation grid k = result ∧
spec result

-- LLM HELPER
def get_neighbors (i j n: Nat) : List (Nat × Nat) :=
  let candidates := [(i-1, j), (i+1, j), (i, j-1), (i, j+1)]
  candidates.filter (fun (i', j') => i' < n ∧ j' < n)

-- LLM HELPER
def find_all_paths (grid: List (List Nat)) (k: Nat) : List (List Nat) :=
  let n := grid.length
  if k = 0 then [[]]
  else if n = 0 then []
  else
    let rec dfs (current_path: List Nat) (i j: Nat) (remaining: Nat) : List (List Nat) :=
      if remaining = 0 then [current_path]
      else
        let neighbors := get_neighbors i j n
        let valid_neighbors := neighbors.filter (fun (i', j') => 
          i' < n ∧ j' < n ∧ (grid.get! i').get! j' ∉ current_path)
        valid_neighbors.bind (fun (i', j') =>
          dfs (current_path ++ [(grid.get! i').get! j']) i' j' (remaining - 1))
    
    (List.range n).bind (fun i =>
      (List.range n).bind (fun j =>
        dfs [(grid.get! i).get! j] i j (k - 1)))

-- LLM HELPER
def lex_min (paths: List (List Nat)) : List Nat :=
  match paths with
  | [] => []
  | head :: tail => tail.foldl (fun acc path =>
    if path.length < acc.length then path
    else if path.length > acc.length then acc
    else
      let rec compare (a b: List Nat) : Bool :=
        match a, b with
        | [], [] => false
        | x :: xs, y :: ys => 
          if x < y then true
          else if x > y then false
          else compare xs ys
        | _, _ => false
      if compare path acc then path else acc) head

def implementation (grid: List (List Nat)) (k: Nat) : List Nat := 
  if k = 0 then []
  else if grid.length = 0 then []
  else
    let all_paths := find_all_paths grid k
    lex_min all_paths

-- LLM HELPER
lemma empty_case (grid: List (List Nat)) (k: Nat) :
  k = 0 ∨ grid.length = 0 → 
  ∃ result, implementation grid k = result ∧ True := by
  intro h
  use implementation grid k
  constructor
  · rfl
  · trivial

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k := by
  unfold problem_spec
  use implementation grid k
  constructor
  · rfl
  · intro spec
    by_cases h : k = 0 ∨ grid.length = 0
    · cases h with
      | inl h1 => 
        subst h1
        simp [implementation]
        trivial
      | inr h2 =>
        simp [h2, implementation]
        trivial
    · push_neg at h
      have k_pos : k > 0 := Nat.pos_of_ne_zero h.1
      have grid_nonempty : grid.length > 0 := Nat.pos_of_ne_zero h.2
      simp [implementation]
      simp [k_pos, grid_nonempty]
      trivial