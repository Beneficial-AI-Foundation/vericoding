-- <vc-preamble>
def get_strings (s : String) : String := sorry

def is_alpha (c : Char) : Bool := sorry

def to_lower (c : Char) : Char := sorry

structure SegmentInfo where
  letter : Char
  stars : String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse_segment (s : String) : Option SegmentInfo := sorry

theorem get_strings_format_valid (s : String) (h : s ≠ "") :
  let result := get_strings s
  let segments := result.splitOn ","
  ∀ part ∈ segments,
  part ≠ "" →
  match parse_segment part with
  | some info => 
    is_alpha info.letter ∧ 
    ∀ c ∈ info.stars.data, c = '*'
  | none => False := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_strings_count_matches_freq (s : String) (h : s ≠ "") :
  let result := get_strings s
  let segments := result.splitOn "," |>.filter (·≠ "")
  ∀ seg ∈ segments,
  match parse_segment seg with
  | some info =>
    let count := s.data.filter (fun c => to_lower c = to_lower info.letter) |>.length
    info.stars.length = count
  | none => False := sorry

theorem get_strings_empty :
  get_strings "" = "" := sorry

theorem get_strings_example :
  get_strings "Chicago" = "c:**,h:*,i:*,a:*,g:*,o:*" := sorry

/-
info: 'c:**,h:*,i:*,a:*,g:*,o:*'
-/
-- #guard_msgs in
-- #eval get_strings "Chicago"

/-
info: 'b:*,a:*,n:*,g:*,k:**,o:*'
-/
-- #guard_msgs in
-- #eval get_strings "Bangkok"

/-
info: 'l:*,a:**,s:**,v:*,e:*,g:*'
-/
-- #guard_msgs in
-- #eval get_strings "Las Vegas"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded