import Mathlib
-- <vc-preamble>
def find_newline (s : String) (start : Nat) : Nat :=
  if start ≥ s.length then s.length
  else if s.data[start]! = '\n' then start
  else find_newline s (start + 1)

def is_valid_positive_integer (s : String) : Bool :=
  s.length > 0 && (List.all (List.range s.length) (fun i => s.data[i]! ≥ '0' && s.data[i]! ≤ '9')) && s ≠ "0"

def string_to_int_helper (s : String) (pos : Nat) (acc : Int) : Int :=
  if pos ≥ s.length then 
    if acc = 0 then 1 else acc
  else if s.data[pos]! ≥ '0' && s.data[pos]! ≤ '9' then
    string_to_int_helper s (pos + 1) (acc * 10 + (s.data[pos]!.toNat - '0'.toNat))
  else
    if acc = 0 then 1 else acc

def string_to_int (s : String) : Int :=
  string_to_int_helper s 0 0

def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.data[i]! = '\n') ∧
  (let newline_pos := find_newline stdin_input 0
   let K_str := stdin_input.take newline_pos
   is_valid_positive_integer K_str = true) ∧
  (let newline_pos := find_newline stdin_input 0
   let K_str := stdin_input.take newline_pos
   let K := string_to_int K_str
   1 ≤ K ∧ K ≤ 100) ∧
  (let newline_pos := find_newline stdin_input 0
   let rest := stdin_input.drop (newline_pos + 1)
   let S := if rest.length > 0 ∧ rest.data[rest.length - 1]! = '\n' then rest.take (rest.length - 1) else rest
   1 ≤ S.length ∧ S.length ≤ 100 ∧ ∀ i, 0 ≤ i ∧ i < S.length → 'a' ≤ S.data[i]! ∧ S.data[i]! ≤ 'z')

def ExtractK (stdin_input : String) : Int :=
  let newline_pos := find_newline stdin_input 0
  let K_str := stdin_input.take newline_pos
  string_to_int K_str

def ExtractS (stdin_input : String) : String :=
  let newline_pos := find_newline stdin_input 0
  let rest := stdin_input.drop (newline_pos + 1)
  if rest.length > 0 ∧ rest.data[rest.length - 1]! = '\n' then rest.take (rest.length - 1) else rest

def CorrectOutput (stdin_input : String) (result : String) : Prop :=
  let K := ExtractK stdin_input
  let S := ExtractS stdin_input
  K ≥ 1 ∧ K ≤ 100 ∧
  S.length ≥ 1 ∧ S.length ≤ 100 ∧
  (∀ i, 0 ≤ i ∧ i < S.length → 'a' ≤ S.data[i]! ∧ S.data[i]! ≤ 'z') ∧
  (S.length ≤ K.toNat → result = S ++ "\n") ∧
  (S.length > K.toNat → result = S.take K.toNat ++ "..." ++ "\n")

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for the solve function proof

lemma extract_k_bounds (stdin_input : String) (h : ValidInput stdin_input) :
    1 ≤ ExtractK stdin_input ∧ ExtractK stdin_input ≤ 100 := by
  unfold ValidInput at h
  obtain ⟨_, _, _, h_k_bounds, _⟩ := h
  exact h_k_bounds

lemma extract_s_properties (stdin_input : String) (h : ValidInput stdin_input) :
    let S := ExtractS stdin_input
    1 ≤ S.length ∧ S.length ≤ 100 ∧ ∀ i, 0 ≤ i ∧ i < S.length → 'a' ≤ S.data[i]! ∧ S.data[i]! ≤ 'z' := by
  unfold ValidInput at h
  obtain ⟨_, _, _, _, h_s⟩ := h
  exact h_s
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let K := ExtractK stdin_input
  let S := ExtractS stdin_input
  if S.length ≤ K.toNat then
    S ++ "\n"
  else
    S.take K.toNat ++ "..." ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  CorrectOutput stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond CorrectOutput solve
  simp only [solve_precond] at h_precond
  let K := ExtractK stdin_input
  let S := ExtractS stdin_input
  
  -- Get bounds from precondition
  have h_k_bounds := extract_k_bounds stdin_input h_precond
  have h_s_props := extract_s_properties stdin_input h_precond
  
  constructor
  · exact h_k_bounds.1
  constructor
  · exact h_k_bounds.2
  constructor
  · exact h_s_props.1
  constructor
  · exact h_s_props.2.1
  constructor
  · exact h_s_props.2.2
  constructor
  · intro h_len_le
    simp [h_len_le]
  · intro h_len_gt
    simp [h_len_gt]
-- </vc-theorems>
