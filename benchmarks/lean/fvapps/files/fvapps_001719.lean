-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_bc (url : String) (separator : String) : String :=
  sorry

def containsStr (s : String) (sub : String) : Bool :=
  sorry

def findStr (s : String) (sub : String) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_bc_structure (paths : List String) (separator : String)
  (h1 : paths.length ≥ 1) (h2 : paths.length ≤ 5) :
  let url := "mysite.com/" ++ String.intercalate "/" paths
  let result := generate_bc url separator;
  (result.startsWith "<a href=\"/\">HOME</a>" ∨
   result.startsWith "<span class=\"active\">HOME</span>") ∧
  result.endsWith "</span>" ∧
  (containsStr result "<span class=\"active\">") ∧
  ((result.split (· == separator.get! 0)).length ≥ 1) :=
sorry

theorem generate_bc_protocol_stripping (url : String)
  (h : containsStr url "http://" ∨ containsStr url "https://") :
  let result := generate_bc url "/";
  ¬containsStr result "http://" ∧
  ¬containsStr result "https://" :=
sorry

theorem generate_bc_long_segments (path : String)
  (h : path.length > 30) :
  let url := "mysite.com/" ++ path
  let result := generate_bc url " > "
  let spans := result.split (· == '>')
  let lastSpan := spans[spans.length - 1]'(by sorry)
  let content := (lastSpan.split (· == '>')).getLast!;
  content.length < path.length :=
sorry

theorem generate_bc_href_validity (paths : List String)
  (h1 : paths.length ≥ 2) (h2 : paths.length ≤ 5) :
  let url := "mysite.com/" ++ String.intercalate "/" paths
  let result := generate_bc url " : "
  let segments := (result.split (· == ':')).dropLast;
  ∀ s ∈ segments,
    s.startsWith "<a href=\"/\"" ∧
    s.endsWith "</a>" ∧
    (findStr s "\">").isSome :=
sorry
-- </vc-theorems>