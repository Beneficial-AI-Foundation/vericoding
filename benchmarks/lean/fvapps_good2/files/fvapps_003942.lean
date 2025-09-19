-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_check (s : String) : Bool :=
sorry

def isOpening (c : Char) : Bool :=
sorry

def isClosing (c : Char) : Bool :=
sorry

def matching (o c : Char) : Bool :=
sorry

def countOpening (s : String) : Nat :=
sorry

def countClosing (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_valid :
  group_check "" = true :=
sorry

theorem simple_pair_valid (o c : Char) :
  isOpening o → matching o c →
  group_check (String.mk [o, c]) = true :=
sorry

theorem valid_brackets_equal_counts {s : String} :
  group_check s = true →
  countOpening s = countClosing s :=
sorry

theorem only_opening_invalid {s : String} :
  s ≠ "" →
  (∀ c ∈ s.data, isOpening c) →
  group_check s = false :=
sorry

theorem only_closing_invalid {s : String} :
  s ≠ "" →
  (∀ c ∈ s.data, isClosing c) →
  group_check s = false :=
sorry

theorem nested_brackets_valid {opens : List Char} :
  opens ≠ [] →
  (∀ c ∈ opens, isOpening c) →
  let closes := (opens.map (λ o => match o with
    | '(' => ')'
    | '{' => '}'
    | '[' => ']'
    | _ => ' ')).reverse
  group_check (String.mk (opens ++ closes)) = true :=
sorry
-- </vc-theorems>