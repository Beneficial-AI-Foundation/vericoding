-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sursurungal (s : String) : String :=
sorry

def containsDigit (s : String) (d : Nat) : Prop :=
sorry

def containsWordAfterNumber (s : String) (n : Nat) (w : String) : Prop :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sursurungal_preserves_numbers {s : String} :
  ∀ n : Nat, containsDigit s n → containsDigit (sursurungal s) n :=
sorry

theorem word_transformation_rules {s : String} (n : Nat) (w : String) :
  containsWordAfterNumber (sursurungal s) n w →
  match n with
  | 1 => ¬(w.startsWith "bu") ∧ ¬(w.startsWith "ga") ∧ ¬(w.endsWith "zo")
  | 2 => w.startsWith "bu" ∧ ¬(w.startsWith "ga") ∧ ¬(w.endsWith "zo")
  | n => if n ≤ 9
        then ¬(w.startsWith "bu") ∧ ¬(w.startsWith "ga") ∧ w.endsWith "zo"
        else w.startsWith "ga" ∧ w.endsWith "ga" ∧ ¬(w.endsWith "zo") :=
sorry

theorem unchanged_text_without_numbers (s : String) :
  (∀ n : Nat, ¬containsDigit s n) →
  sursurungal s = s :=
sorry
-- </vc-theorems>