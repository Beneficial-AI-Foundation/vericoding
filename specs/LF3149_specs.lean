-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def highlight (s : String) : String :=
sorry

def colorFor (c : Char) : String :=
sorry

def String.count (s : String) (sub : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem letter_get_correct_colors (c : Char) (h: c ∈ ['F', 'L', 'R']):
  let color :=
    match c with
    | 'F' => "pink"
    | 'L' => "red"
    | 'R' => "green"
    | _ => ""
  colorFor c = color
  :=
sorry

theorem numbers_get_orange (c : Char) (h : c.isDigit) :
  colorFor c = "orange" :=
sorry

theorem consecutive_chars_single_span (s : String) (h: s.all (· = s.get! 0)) :
  (highlight s).count "<span" = 1 :=
sorry

theorem highlight_maintains_content (s : String) :
  let stripped := (highlight s).replace "<span" "" |>.replace "</span" "" |>.replace "style=\"color: pink\"" ""
                   |>.replace "style=\"color: red\"" "" |>.replace "style=\"color: green\"" ""
                   |>.replace "style=\"color: orange\"" ""
  stripped = s :=
sorry
-- </vc-theorems>