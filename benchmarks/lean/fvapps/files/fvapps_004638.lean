-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def html_end_tag_by_start_tag (start_tag: String) : String :=
  sorry

def is_valid_tag_char (c: Char) : Bool :=
  sorry

def is_valid_tag_first_char (c: Char) : Bool :=
  sorry

def is_valid_attr_name_char (c: Char) : Bool :=
  sorry

def is_valid_attr_value_char (c: Char) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem html_end_tag_starts_with_close : ∀ (start_tag : String),
  (html_end_tag_by_start_tag start_tag).startsWith "</" = true :=
sorry

theorem html_end_tag_ends_with_angle : ∀ (start_tag : String),
  (html_end_tag_by_start_tag start_tag).endsWith ">" = true :=
sorry

theorem html_end_tag_matches_start : ∀ (start_tag : String),
  let start_name := (start_tag.drop 1).splitOn " " |>.head!.dropRight 1
  let end_name := (html_end_tag_by_start_tag start_tag).drop 2 |>.dropRight 1
  start_name = end_name :=
sorry

theorem html_end_tag_no_attributes : ∀ (start_tag : String),
  ¬(html_end_tag_by_start_tag start_tag).contains ' ' :=
sorry
-- </vc-theorems>