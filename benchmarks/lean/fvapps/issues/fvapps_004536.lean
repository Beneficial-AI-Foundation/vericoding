-- <vc-preamble>
def Node.data : Node → Int
  | mk d _ => d

def get_nth (head : Option Node) (n : Nat) : Option Node :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_list : List Int → Option Node :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_nth_valid_index_returns_correct_value (head : Option Node) (values : List Int) (index : Nat) :
  head = build_list values →
  index < values.length →
  ∃ (h : index < values.length), 
    (get_nth head index).map Node.data = some (values.get ⟨index, h⟩) :=
  sorry

theorem get_nth_invalid_index_returns_none (head : Option Node) (values : List Int) (index : Nat) : 
  head = build_list values →
  index ≥ values.length →
  get_nth head index = none :=
  sorry

theorem get_nth_empty_list_returns_none (index : Nat) :
  get_nth none index = none :=
  sorry

theorem get_nth_zero_returns_first (head : Option Node) (values : List Int) :
  head = build_list values →
  values ≠ [] →
  (get_nth head 0).map Node.data = some (values.head!) :=
  sorry

theorem get_nth_last_returns_last (head : Option Node) (values : List Int) :
  head = build_list values →
  values ≠ [] →
  ∃ (h : values.length - 1 < values.length),
    (get_nth head (values.length - 1)).map Node.data = some (values.get ⟨values.length - 1, h⟩) :=
  sorry
-- </vc-theorems>