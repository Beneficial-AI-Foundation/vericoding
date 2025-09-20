-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def simplify_path (s : String) : String :=
sorry

def is_valid_path_segment (s : String) : Bool :=
sorry

def splitString (s : String) (c : Char) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dot_references_resolve
  {segments : List String}
  (valid_segs : ∀ s ∈ segments, s = "." ∨ s = ".." ∨ is_valid_path_segment s) :
  let path := "/" ++ String.intercalate "/" segments
  let result := simplify_path path
  result.startsWith "/" ∧ "." ∉ splitString result '/'
  :=
sorry

theorem redundant_slashes
  (slashes : String)
  (h : ∀ c ∈ slashes.toList, c = '/') :
  simplify_path slashes = "/"
  :=
sorry

theorem idempotent
  {segments : List String}
  (valid_segs : ∀ s ∈ segments, is_valid_path_segment s) :
  let path := "/" ++ String.intercalate "/" segments
  let once := simplify_path path
  simplify_path once = once
  :=
sorry

theorem root_path :
  simplify_path "/" = "/"
  :=
sorry
-- </vc-theorems>