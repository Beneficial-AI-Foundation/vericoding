def get_lucky_string (a b : String) : String := sorry

def isDigitChar (c : Char) : Bool := 
  '0' ≤ c ∧ c ≤ '9'

-- <vc-helpers>
-- </vc-helpers>

def isLuckyChar (c : Char) : Bool :=
  c = '4' ∨ c = '7'

theorem lucky_string_only_lucky_chars (a b : String) 
  (h_a : ∀ c ∈ a.data, isDigitChar c)
  (h_b : ∀ c ∈ b.data, isDigitChar c) :
  ∀ c ∈ (get_lucky_string a b).data, isLuckyChar c := sorry

theorem lucky_string_seven_before_four (a b : String)
  (h_a : ∀ c ∈ a.data, isDigitChar c)
  (h_b : ∀ c ∈ b.data, isDigitChar c)
  (h_has_both : '7' ∈ (get_lucky_string a b).data ∧ '4' ∈ (get_lucky_string a b).data) :
  ∃ pos_seven pos_four, 
    pos_seven < pos_four ∧
    (get_lucky_string a b).data.get! pos_seven = '7' ∧
    (get_lucky_string a b).data.get! pos_four = '4' := sorry

theorem lucky_string_length (a b : String)
  (h_a : ∀ c ∈ a.data, isDigitChar c)
  (h_b : ∀ c ∈ b.data, isDigitChar c) :
  (get_lucky_string a b).length ≤ a.length + b.length := sorry

theorem lucky_string_deterministic (a b : String)
  (h_a : ∀ c ∈ a.data, isDigitChar c)
  (h_b : ∀ c ∈ b.data, isDigitChar c) :
  get_lucky_string a b = get_lucky_string a b := sorry

theorem lucky_string_identical_inputs (s : String)
  (h : ∀ c ∈ s.data, isDigitChar c) :
  get_lucky_string s s = get_lucky_string s s := sorry

theorem lucky_string_commutative (a b : String)
  (h_a : ∀ c ∈ a.data, isDigitChar c)
  (h_b : ∀ c ∈ b.data, isDigitChar c) :
  get_lucky_string a b = get_lucky_string b a := sorry

theorem lucky_string_preserves_counts (s : String)
  (h : ∀ c ∈ s.data, isDigitChar c)
  (h_nonempty : s.length > 0) :
  let result := get_lucky_string s s
  let count_4s := (s.data.filter (· = '4')).length
  let count_7s := (s.data.filter (· = '7')).length
  (result.data.filter (· = '4')).length ≤ 2 * count_4s ∧
  (result.data.filter (· = '7')).length ≤ 2 * count_7s := sorry

/-
info: '7'
-/
-- #guard_msgs in
-- #eval get_lucky_string "4" "7"

/-
info: '74'
-/
-- #guard_msgs in
-- #eval get_lucky_string "435" "479"

/-
info: '777744'
-/
-- #guard_msgs in
-- #eval get_lucky_string "1675475" "9756417"

-- Apps difficulty: interview
-- Assurance level: unguarded