def problem_spec
-- function signature
(implementation: String → List Int)
-- inputs
(paren_string: String)
:=
-- spec
let spec (result: List Int) :=
let paren_space_split := paren_string.split (fun x => x = ' ');
result.length = paren_space_split.length ∧
∀ i, i < result.length →
let group := paren_space_split[i]!;
balanced_paren_non_computable group '(' ')' →
0 < result[i]! ∧ count_max_paren_depth group = result[i]!.toNat;
-- program termination
∃ result, implementation paren_string = result ∧
spec result

-- LLM HELPER
def balanced_paren_non_computable (s: String) (open: Char) (close: Char) : Prop :=
∃ (depth: Nat), 
  (∀ i, i < s.length → 
    let c := s.get ⟨i, by assumption⟩
    c = open ∨ c = close ∨ (c ≠ open ∧ c ≠ close)) ∧
  (s.toList.foldl (fun acc c => 
    if c = open then acc + 1 
    else if c = close then acc - 1 
    else acc) 0 = 0)

-- LLM HELPER
def count_max_paren_depth (s: String) : Nat :=
s.toList.foldl (fun acc c => 
  let (curr_depth, max_depth) := acc
  if c = '(' then 
    let new_depth := curr_depth + 1
    (new_depth, max (new_depth) max_depth)
  else if c = ')' then 
    (curr_depth - 1, max_depth)
  else 
    acc) (0, 0) |>.2

-- LLM HELPER
def compute_depth (group: String) : Int :=
Int.ofNat (count_max_paren_depth group)

def implementation (paren_string: String) : List Int := 
let paren_space_split := paren_string.split (fun x => x = ' ')
paren_space_split.map compute_depth

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  unfold problem_spec
  use (paren_string.split (fun x => x = ' ')).map compute_depth
  constructor
  · rfl
  · constructor
    · simp [implementation]
      exact list_map_length compute_depth (paren_string.split (fun x => x = ' '))
    · intro i hi
      simp [implementation] at hi
      intro h_balanced
      rw [List.get_map]
      constructor
      · unfold compute_depth
        simp [Int.ofNat_pos]
        unfold count_max_paren_depth
        simp
        sorry
      · unfold compute_depth
        simp [Int.toNat_of_nonneg]
        sorry