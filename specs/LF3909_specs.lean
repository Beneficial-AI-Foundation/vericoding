-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsUpper (c : Char) : Bool :=
sorry

def IsLower (c : Char) : Bool :=
sorry

def swapcase (c : Char) : Char :=
sorry

def sc (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sc_subset (s : String) :
  ∀ (c : Char), c ∈ (sc s).data → c ∈ s.data :=
sorry

theorem sc_length (s : String) :
  (sc s).length ≤ s.length :=
sorry

theorem sc_swapcase_pairs (s : String) :
  ∀ (c : Char), c ∈ (sc s).data → swapcase c ∈ (sc s).data :=
sorry

theorem sc_all_upper (s : String) :
  (∀ (c : Char), c ∈ s.data → IsUpper c) → sc s = "" :=
sorry

theorem sc_all_lower (s : String) :
  (∀ (c : Char), c ∈ s.data → IsLower c) → sc s = "" :=
sorry

theorem sc_empty :
  sc "" = "" :=
sorry

theorem sc_idempotent (s : String) :
  sc (sc s) = sc s :=
sorry
-- </vc-theorems>