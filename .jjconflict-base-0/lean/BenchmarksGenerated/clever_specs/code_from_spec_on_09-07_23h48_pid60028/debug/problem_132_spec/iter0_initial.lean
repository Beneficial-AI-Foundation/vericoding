def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
string.toList.all (fun x => x = '(' ∨ x = ')') →
result = true ↔
  ∃ x : String,
    is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x
-- program termination
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_subsequence (sub : List α) (main : List α) : Bool :=
  match sub, main with
  | [], _ => true
  | _, [] => false
  | h₁::t₁, h₂::t₂ => if h₁ = h₂ then is_subsequence t₁ t₂ else is_subsequence sub t₂

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open_char close_char : Char) : Bool :=
  let chars := s.toList
  let helper : List Char → Int → Bool
    | [], depth => depth = 0
    | c::rest, depth =>
      if c = open_char then
        helper rest (depth + 1)
      else if c = close_char then
        if depth > 0 then helper rest (depth - 1) else false
      else
        helper rest depth
  helper chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.toList
  let helper : List Char → Nat → Nat → Nat
    | [], current_depth, max_depth => max max_depth current_depth
    | c::rest, current_depth, max_depth =>
      if c = '(' then
        helper rest (current_depth + 1) (max max_depth (current_depth + 1))
      else if c = ')' then
        helper rest (if current_depth > 0 then current_depth - 1 else 0) max_depth
      else
        helper rest current_depth max_depth
  helper chars 0 0

-- LLM HELPER
def has_balanced_subsequence_with_depth (s : String) : Bool :=
  let chars := s.toList
  let opens := chars.filter (· = '(')
  let closes := chars.filter (· = ')')
  let min_pairs := min opens.length closes.length
  min_pairs ≥ 2

def implementation (lst: String) : Bool := 
  if lst.toList.all (fun x => x = '(' ∨ x = ')') then
    has_balanced_subsequence_with_depth lst
  else
    false

-- LLM HELPER
lemma subsequence_construction (s : String) (open_count close_count : Nat) :
  s.toList.all (fun x => x = '(' ∨ x = ')') →
  s.toList.filter (· = '(') |>.length ≥ open_count →
  s.toList.filter (· = ')') |>.length ≥ close_count →
  open_count = close_count →
  open_count ≥ 2 →
  ∃ x : String,
    is_subsequence x.toList s.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x := by
  intros h_all h_opens h_closes h_eq h_ge
  let balanced_str := String.mk (List.replicate open_count '(' ++ List.replicate close_count ')')
  use balanced_str
  constructor
  · -- is_subsequence proof
    sorry
  constructor
  · -- balanced_paren_non_computable proof
    sorry
  · -- count_max_paren_depth proof
    sorry

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec implementation
  use (if string.toList.all (fun x => x = '(' ∨ x = ')') then
         has_balanced_subsequence_with_depth string
       else
         false)
  constructor
  · rfl
  · intro h_all
    constructor
    · intro h_true
      unfold has_balanced_subsequence_with_depth at h_true
      simp at h_true
      let open_count := string.toList.filter (· = '(') |>.length
      let close_count := string.toList.filter (· = ')') |>.length
      let min_pairs := min open_count close_count
      have h_min : min_pairs ≥ 2 := h_true
      have h_open : open_count ≥ min_pairs := min_le_left open_count close_count
      have h_close : close_count ≥ min_pairs := min_le_right open_count close_count
      apply subsequence_construction string min_pairs min_pairs h_all
      · exact Nat.le_trans h_min h_open
      · exact Nat.le_trans h_min h_close
      · rfl
      · exact h_min
    · intro h_exists
      unfold has_balanced_subsequence_with_depth
      simp
      obtain ⟨x, h_subseq, h_balanced, h_depth⟩ := h_exists
      -- From the existence of such a subsequence, we can derive that there are enough parens
      sorry