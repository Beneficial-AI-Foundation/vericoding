-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Char.alpha? (c : Char) : Bool := sorry

def Char.ascii? (c : Char) : Bool :=
sorry

def one_down (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def String.containsAsciiLetter (s : String) : Bool :=
  s.data.any (fun c => c.ascii? && c.alpha?)

theorem one_down_maintains_string_type {s : String} :
  let res := one_down s
  ∃ s', res = s' :=
sorry

theorem one_down_differs_if_contains_ascii_letter {s : String} :
  s.containsAsciiLetter →
  one_down s ≠ s :=
sorry

theorem one_down_preserves_length {s : String} :
  (one_down s).length = s.length :=
sorry

theorem one_down_preserves_non_letters {s : String} {i : Fin s.length} :
  ¬(s.data[i.val]?.map (·.alpha?) |>.getD false) →
  (one_down s).data[i.val]? = s.data[i.val]? :=
sorry

theorem one_down_non_string_input {α : Type} [ToString α] (x : α) :
  one_down (toString x) = "Input is not a string" :=
sorry
-- </vc-theorems>