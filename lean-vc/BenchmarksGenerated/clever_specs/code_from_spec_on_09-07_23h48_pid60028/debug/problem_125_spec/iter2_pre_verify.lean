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
  else if grid.length = 0 then []
  else
    let all_paths := get_all_paths grid k
    lex_min all_paths

-- LLM HELPER
lemma get_neighbors_valid (grid: List (List Nat)) (i j: Nat) :
  ∀ p ∈ get_neighbors grid i j, p.1 < grid.length ∧ p.2 < grid.length := by
  intro p hp
  simp [get_neighbors] at hp
  exact hp

-- LLM HELPER
lemma lex_min_is_minimum (paths: List (List Nat)) (p: List Nat) :
  p ∈ paths → lex_min paths ≤ p := by
  intro hp
  induction paths with
  | nil => contradiction
  | cons head tail ih =>
    simp [lex_min]
    cases hp with
    | head => 
      by_cases h : head ≤ lex_min tail
      · simp [h]
      · simp [h]
        exact le_refl head
    | tail hp_tail =>
      by_cases h : head ≤ lex_min tail
      · simp [h]
        exact le_trans (ih hp_tail) (le_refl _)
      · simp [h]
        exact ih hp_tail

-- LLM HELPER
lemma implementation_correct_base_case (grid: List (List Nat)) :
  k = 0 → implementation grid k = [] := by
  intro h
  simp [implementation, h]

-- LLM HELPER
lemma implementation_gives_valid_path (grid: List (List Nat)) (k: Nat) :
  grid.length > 0 → k > 0 → 
  (∀ i, i < grid.length → (grid[i]!).length = grid.length) →
  let result := implementation grid k
  ∃ some_path, some_path ∈ get_all_paths grid k ∧ result = lex_min (get_all_paths grid k) := by
  intro h_grid_nonempty h_k_pos h_square
  use (get_all_paths grid k).head!
  constructor
  · simp [get_all_paths]
    split
    · simp
    · split
      · simp [List.join]
        use 0, 0
        simp
      · simp [List.join]
        use 0, 0
        simp
  · rfl

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
      else
        simp [implementation]
        split
        · contradiction
        · simp at h_len
          simp [get_all_paths]
          split
          · contradiction
          · split
            · simp [List.join]
              use 0, 0
              simp
              constructor
              · simp [h_square]
              · intro h_multi
                simp [implementation] at h_len
                contradiction
            · simp [List.join]
              use 0, 0
              simp
              constructor
              · simp [h_square]
              · intro h_multi
                simp [implementation] at h_len
                split at h_len
                · simp [lex_min] at h_len
                  split at h_len
                  · contradiction
                  · simp [get_all_paths] at h_len
                    split at h_len
                    · simp at h_len
                      contradiction
                    · split at h_len
                      · simp [List.join] at h_len
                        contradiction
                      · simp [List.join] at h_len
                        use 0, 0
                        simp
                        constructor
                        · simp [h_square]
                        · intro
                          use 0, 0
                          simp
                          constructor
                          · simp [h_square]
                          · constructor
                            · simp [get_neighbors]
                              simp [List.filter]
                              simp [h_square]
                            · simp [problem_spec.is_valid_path]
                              intro h_drop_len
                              simp [List.drop] at h_drop_len
                              simp [lex_min] at h_drop_len
                              split at h_drop_len
                              · contradiction
                              · simp [get_all_paths] at h_drop_len
                                split at h_drop_len
                                · simp at h_drop_len
                                  contradiction
                                · split at h_drop_len
                                  · simp [List.join] at h_drop_len
                                    contradiction
                                  · simp [List.join] at h_drop_len
                                    use 0, 0
                                    simp
                                    constructor
                                    · simp [h_square]
                                    · intro
                                      use 0, 0
                                      simp
                                      constructor
                                      · simp [h_square]
                                      · constructor
                                        · simp [get_neighbors]
                                          simp [List.filter]
                                          simp [h_square]
                                        · simp [problem_spec.is_valid_path]
                                          intro
                                          simp [List.drop]
                                          use 0, 0
                                          simp
                                          simp [h_square]
                · simp [get_all_paths] at h_len
                  split at h_len
                  · simp [lex_min] at h_len
                    contradiction
                  · split at h_len
                    · simp [List.join, lex_min] at h_len
                      contradiction
                    · simp [List.join, lex_min] at h_len
                      use 0, 0
                      simp
                      constructor
                      · simp [h_square]
                      · intro
                        use 0, 0
                        simp
                        constructor
                        · simp [h_square]
                        · constructor
                          · simp [get_neighbors]
                            simp [List.filter]
                            simp [h_square]
                          · simp [problem_spec.is_valid_path]
                            intro
                            simp [List.drop]
                            use 0, 0
                            simp
                            simp [h_square]
    · intro path h_path_valid
      simp [lexographically_less]
      constructor
      · simp [implementation]
        split
        · simp [problem_spec.is_valid_path] at h_path_valid
          simp [h_path_valid]
        · split
          · simp [problem_spec.is_valid_path] at h_path_valid
            simp [h_path_valid]
          · simp [lex_min, get_all_paths]
            split
            · simp [problem_spec.is_valid_path] at h_path_valid
              simp [h_path_valid]
            · split
              · simp [List.join, lex_min]
                simp [problem_spec.is_valid_path] at h_path_valid
                simp [h_path_valid]
              · simp [List.join, lex_min]
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
              split
              · simp [problem_spec.is_valid_path] at h_path_valid
                simp [h_path_valid]
              · split
                · simp [List.join, lex_min]
                  simp [problem_spec.is_valid_path] at h_path_valid
                  simp [h_path_valid]
                · simp [List.join, lex_min]
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
              split
              · simp [problem_spec.is_valid_path] at h_path_valid
                simp [h_path_valid]
              · split
                · simp [List.join, lex_min]
                  simp [problem_spec.is_valid_path] at h_path_valid
                  simp [h_path_valid]
                · simp [List.join, lex_min]
                  simp [problem_spec.is_valid_path] at h_path_valid
                  simp [h_path_valid]