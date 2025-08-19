def problem_spec
-- function signature
(implementation: List Rat → (Rat × Rat))
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: (Rat × Rat)) :=
2 ≤ numbers.length →
(let (smaller, larger) := result;
let abs_diff := abs (larger - smaller);
smaller ≤ larger ∧
smaller ∈ numbers ∧
larger ∈ numbers ∧
(∀ x y, x ∈ numbers → y ∈ numbers → abs_diff ≤ abs (x - y)) ∧
(smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_closest_pair_aux (numbers: List Rat) : (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| x :: xs =>
  let init_pair := (x, x)
  let init_diff := (0 : Rat)
  xs.foldl (fun acc y =>
    let (best_smaller, best_larger) := acc
    let current_diff := abs (best_larger - best_smaller)
    let new_diff := abs (x - y)
    if new_diff < current_diff then
      if x ≤ y then (x, y) else (y, x)
    else if new_diff = current_diff then
      let candidate := if x ≤ y then (x, y) else (y, x)
      if candidate.1 < best_smaller ∨ (candidate.1 = best_smaller ∧ candidate.2 ≤ best_larger) then
        candidate
      else
        acc
    else
      acc
  ) init_pair

-- LLM HELPER
def find_min_diff_pairs (numbers: List Rat) : List (Rat × Rat) :=
match numbers with
| [] => []
| [x] => [(x, x)]
| _ =>
  let all_pairs := List.bind numbers (fun x => List.map (fun y => if x ≤ y then (x, y) else (y, x)) numbers)
  let min_diff := List.foldl (fun acc pair => min acc (abs (pair.2 - pair.1))) (abs (List.head! numbers - List.head! numbers)) all_pairs
  List.filter (fun pair => abs (pair.2 - pair.1) = min_diff) all_pairs

def implementation (numbers: List Rat): (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| x :: xs =>
  let all_pairs := List.bind numbers (fun a => List.map (fun b => if a ≤ b then (a, b) else (b, a)) numbers)
  let valid_pairs := List.filter (fun pair => pair.1 ∈ numbers ∧ pair.2 ∈ numbers) all_pairs
  match valid_pairs with
  | [] => (x, x)
  | p :: ps =>
    List.foldl (fun acc pair =>
      let acc_diff := abs (acc.2 - acc.1)
      let pair_diff := abs (pair.2 - pair.1)
      if pair_diff < acc_diff then pair
      else if pair_diff = acc_diff then
        if pair.1 < acc.1 ∨ (pair.1 = acc.1 ∧ pair.2 ≤ acc.2) then pair else acc
      else acc
    ) p ps

-- LLM HELPER
lemma list_length_ge_two_has_elements (numbers: List Rat) (h: 2 ≤ numbers.length) :
  ∃ x y xs, numbers = x :: y :: xs := by
  cases numbers with
  | nil => simp at h
  | cons a tail =>
    cases tail with
    | nil => simp at h
    | cons b rest => exact ⟨a, b, rest, rfl⟩

-- LLM HELPER
lemma mem_of_mem_bind {α β : Type*} {f : α → List β} {x : α} {y : β} {l : List α} 
  (hx : x ∈ l) (hy : y ∈ f x) : y ∈ List.bind l f := by
  induction l with
  | nil => contradiction
  | cons a tail ih =>
    simp [List.bind]
    cases hx with
    | head => exact Or.inl hy
    | tail h => exact Or.inr (ih h)

-- LLM HELPER
lemma implementation_components_in_list (numbers: List Rat) :
  let result := implementation numbers
  result.1 ∈ numbers ∧ result.2 ∈ numbers := by
  simp [implementation]
  cases numbers with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp [List.bind]
      constructor
      · apply List.mem_cons_self
      · apply List.mem_cons_of_mem
        apply List.mem_cons_self

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    simp [implementation]
    cases numbers with
    | nil => simp at h_len
    | cons x xs =>
      cases xs with  
      | nil => simp at h_len
      | cons y ys =>
        simp
        constructor
        · -- smaller ≤ larger
          simp [List.bind]
          apply le_refl
        constructor
        · -- smaller ∈ numbers  
          simp [List.bind]
          apply List.mem_cons_self
        constructor
        · -- larger ∈ numbers
          simp [List.bind]
          apply List.mem_cons_of_mem
          apply List.mem_cons_self
        constructor
        · -- minimality condition
          intro a b ha hb
          simp [List.bind]
          apply le_refl
        · -- duplicate handling 
          intro h_eq
          simp [List.filter]
          apply Nat.one_le_iff_ne_zero.mpr
          simp