-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode_uri : List String → List String := sorry

def encodings : List (String × String) := [
  (" ", "%20"),
  ("!", "%21"), 
  ("$", "%24"),
  ("%", "%25"),
  ("(", "%28"),
  (")", "%29"),
  ("*", "%2a")
]
-- </vc-definitions>

-- <vc-theorems>
theorem encode_uri_properties (strings : List String) (h : strings ≠ []) :
  let result := encode_uri (strings ++ ["#"]);
  (∀ s ∈ result, s.data ≠ []) ∧ 
  (result.length ≤ strings.length) ∧
  (∀ encoded ∈ result, ∃ orig ∈ strings,
    (List.foldl (fun acc (p : String × String) => 
      acc.replace p.snd p.fst) encoded encodings) = orig) :=
sorry

theorem encode_uri_terminates (strings : List String) 
  (h : ∀ s ∈ strings, s.data ≠ []) :
  encode_uri (strings ++ ["#"] ++ strings) = 
  encode_uri (strings ++ ["#"]) :=
sorry
-- </vc-theorems>