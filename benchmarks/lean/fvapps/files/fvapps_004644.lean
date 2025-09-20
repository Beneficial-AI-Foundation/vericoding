-- <vc-preamble>
def stringToList (s : String) : List Char := s.data

def stringContains (s₁ s₂ : String) : Prop := ∃ pre post : String, s₁ = pre ++ s₂ ++ post
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_special_mult (numbers : List Int) : Int ⊕ String :=
sorry

def parseAsInt (s : String) : Option Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_numbers_only (numbers : List Int)
  (h : ∀ n ∈ numbers, n > 0)
  : ∃ result, (min_special_mult numbers = Sum.inl result ∧ result > 0) :=
sorry

theorem invalid_entries (valid_nums invalid_nums : List String)
  (h1 : invalid_nums.length > 0)
  (h2 : invalid_nums.length ≤ 5)
  (h3 : ∀ n ∈ invalid_nums, ∃ c ∈ (stringToList n), c.isAlpha ∨ c ∈ ['&', '$', '#', '@'])
  (h4 : ∀ n ∈ valid_nums, (parseAsInt n).isSome)
  : let valid_int_nums := valid_nums.filterMap parseAsInt
    ∃ result : String,
    (min_special_mult valid_int_nums = Sum.inr result)
    ∧ (stringContains result (toString invalid_nums.length))
    ∧ (∀ inv ∈ invalid_nums, stringContains result inv) :=
sorry

theorem lcm_properties (numbers : List Int)
  (h1 : numbers.length ≥ 2)
  (h2 : numbers.length ≤ 5)
  (h3 : ∀ n ∈ numbers, n > 0)
  : ∃ result, min_special_mult numbers = Sum.inl result
      ∧ ∀ n ∈ numbers, result % n = 0 :=
sorry
-- </vc-theorems>