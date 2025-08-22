def problem_spec
(implementation: List (List Nat) → Nat → List Nat)
(grid: List (List Nat))
(k: Nat) :=
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a[i]! < b[i]! ∧
  (∀ j, j < i → a[j]! = b[j]!));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path[0]! = (grid[i]!)[j]!) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path[1]! = (grid[i']!)[j']!) ∧
        ((Int.natAbs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (Int.natAbs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid[i]!).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid[i]!)[j]!) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
∃ result, implementation grid k = result ∧
spec result

-- LLM HELPER
def List.join {α : Type*} : List (List α) → List α
  | [] => []
  | xs :: xss => xs ++ List.join xss

-- LLM HELPER
def get_neighbors (grid: List (List Nat)) (i j: Nat) : List (Nat × Nat) :=
  let n := grid.length
  [(i-1, j), (i+1, j), (i, j-1), (i, j+1)].filter (fun p => p.1 < n ∧ p.2 < n)

-- LLM HELPER
def get_all_paths (grid: List (List Nat)) (k: Nat) : List (List Nat) :=
  let n := grid.length
  if k = 0 then [[]]
  else if k = 1 then
    List.join (List.range n |>.map (fun i =>
      List.range n |>.map (fun j => [(grid[i]!)[j]!])))
  else
    let rec build_paths (current_path: List Nat) (last_pos: Nat × Nat) (remaining: Nat) : List (List Nat) :=
      if remaining = 0 then [current_path]
      else
        let neighbors := get_neighbors grid last_pos.1 last_pos.2
        List.join (neighbors.map (fun pos =>
          let new_val := (grid[pos.1]!)[pos.2]!
          build_paths (current_path ++ [new_val]) pos (remaining - 1)))
    List.join (List.range n |>.map (fun i =>
      List.join (List.range n |>.map (fun j =>
        build_paths [(grid[i]!)[j]!] (i, j) (k - 1)))))

-- LLM HELPER
def lex_min (paths: List (List Nat)) : List Nat :=
  match paths with
  | [] => []
  | [p] => p
  | p :: ps => 
    let min_rest := lex_min ps
    if p ≤ min_rest then p else min_rest

def implementation (grid: List (List Nat)) (k: Nat) : List Nat :=
  if k = 0 then []
  else if grid.length = 0 then List.range k |>.map (fun _ => 0)
  else
    let all_paths := get_all_paths grid k
    lex_min all_paths

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k := by
  simp [problem_spec]
  use implementation grid k
  constructor
  · rfl
  · intro h_square h_valid_vals
    constructor
    · simp [problem_spec.is_valid_path]
      intro h_len
      if h : k = 0 then
        simp [implementation, h] at h_len
        contradiction
      else if h_empty : grid.length = 0 then
        simp [implementation, h_empty] at h_len
        contradiction
      else
        simp [implementation, h, h_empty]
        use 0, 0
        constructor
        · simp [h_square]
          constructor
          · simp [Nat.pos_iff_ne_zero]
            exact h_empty
          · constructor
            · simp [Nat.pos_iff_ne_zero]
              exact h_empty
            · simp [lex_min, get_all_paths]
              if h_k1 : k = 1 then
                simp [h_k1]
              else
                simp [h_k1]
        · intro h_gt_one
          simp [lex_min, get_all_paths]
          if h_k1 : k = 1 then
            simp [h_k1] at h_gt_one
            contradiction
          else
            simp [h_k1]
            use 0, 0
            constructor
            · simp [Nat.pos_iff_ne_zero]
              exact h_empty
            · constructor
              · simp [Nat.pos_iff_ne_zero]
                exact h_empty
              · constructor
                · simp [lex_min]
                · simp [problem_spec.is_valid_path]
                  intro h_len2
                  use 0, 0
                  constructor
                  · simp [h_square]
                    constructor
                    · simp [Nat.pos_iff_ne_zero]
                      exact h_empty
                    · constructor
                      · simp [Nat.pos_iff_ne_zero]
                        exact h_empty
                      · simp [lex_min]
                  · intro h_gt_one2
                    simp [lex_min]
                    use 0, 0
                    constructor
                    · simp [Nat.pos_iff_ne_zero]
                      exact h_empty
                    · constructor
                      · simp [Nat.pos_iff_ne_zero]
                        exact h_empty
                      · simp [problem_spec.is_valid_path]
                        intro h_len3
                        use 0, 0
                        constructor
                        · simp [h_square]
                          constructor
                          · simp [Nat.pos_iff_ne_zero]
                            exact h_empty
                          · constructor
                            · simp [Nat.pos_iff_ne_zero]
                              exact h_empty
                            · simp [lex_min]
                        · intro
                          simp [lex_min]
                          use 0, 0
                          constructor
                          · simp [Nat.pos_iff_ne_zero]
                            exact h_empty
                          · constructor
                            · simp [Nat.pos_iff_ne_zero]
                              exact h_empty
                            · simp [problem_spec.is_valid_path]
    · intro path h_path_valid
      simp [problem_spec.lexographically_less]
      constructor
      · simp [implementation]
        split
        · simp [problem_spec.is_valid_path] at h_path_valid
          simp [h_path_valid]
        · split
          · simp [problem_spec.is_valid_path] at h_path_valid
            simp [h_path_valid]
          · simp [lex_min, get_all_paths]
            simp [problem_spec.is_valid_path] at h_path_valid
            simp [h_path_valid]
      · constructor
        · simp [implementation]
          split
          · simp [problem_spec.is_valid_path] at h_path_valid
            simp [h_path_valid]
          · split
            · simp [problem_spec.is_valid_path] at h_path_valid
              simp [h_path_valid]
            · simp [lex_min, get_all_paths]
              simp [problem_spec.is_valid_path] at h_path_valid
              simp [h_path_valid]
        · use 0
          simp [implementation]
          split
          · simp [problem_spec.is_valid_path] at h_path_valid
            simp [h_path_valid]
          · split
            · simp [problem_spec.is_valid_path] at h_path_valid
              simp [h_path_valid]
            · simp [lex_min, get_all_paths]
              simp [problem_spec.is_valid_path] at h_path_valid
              simp [h_path_valid]