-- <vc-preamble>
def DIGS : List String := ["零", "一", "二", "三", "四", "五", "六", "七", "八", "九"]

def POWS : List String := ["", "十", "百", "千", "万"]

def NEG : String := "负"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_chinese_numeral (n : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sign_property {n : Int} :
  n < 0 → (to_chinese_numeral n).startsWith NEG ∧
  n ≥ 0 → ¬(to_chinese_numeral n).startsWith NEG :=
sorry

theorem char_validation {n : Int} :
  ∀ c : Char, c ∈ (to_chinese_numeral n).data →
    c ∈ (NEG.data ++ (String.join DIGS).data ++ (String.join POWS).data) :=
sorry

theorem single_digit {n : Int} (h1 : 1 ≤ n) (h2 : n ≤ 9) :
  to_chinese_numeral n = DIGS[n.toNat - 1]! :=
sorry

theorem teen_numbers {n : Int} (h1 : 10 ≤ n) (h2 : n ≤ 19) :
  (to_chinese_numeral n).startsWith "十" ∧
  (n > 10 → ∃ c : Char, c ∈ (String.join DIGS).data ∧
    (to_chinese_numeral n).data[1]? = some c) :=
sorry
-- </vc-theorems>