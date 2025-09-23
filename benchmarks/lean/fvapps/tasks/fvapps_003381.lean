-- <vc-preamble>
def List.sorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length →
  match l.get? i, l.get? j with
  | some vi, some vj => vi ≤ vj
  | _, _ => True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_char_indices (s : String) (c : Char) : List Nat := sorry

def solve (text : String) (k : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_length (text : String) (k : Nat) (h : text.length > 0) :
  (solve text k).length = max 0 (text.length - min k text.length) :=
sorry

theorem solve_chars_from_original (text : String) (k : Nat) (h : text.length > 0) :
  ∀ c, c ∈ (solve text k).data → c ∈ text.data :=
sorry

theorem solve_maintains_order (text : String) (k : Nat) (h : text.length > 0) :
  ∀ c, c ∈ (solve text k).data →
    let result_indices := get_char_indices (solve text k) c
    let orig_indices := get_char_indices text c
    List.sorted result_indices :=
sorry

theorem solve_k_zero (text : String) (h : text.length > 0) :
  solve text 0 = text :=
sorry

theorem solve_k_length (text : String) (h : text.length > 0) :
  solve text text.length = "" :=
sorry
-- </vc-theorems>