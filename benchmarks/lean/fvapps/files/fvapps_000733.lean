-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_media_types (associations : List (String × String)) (filenames : List String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_associations_gives_unknown (filenames : List String) : 
  determine_media_types [] filenames = List.replicate filenames.length "unknown" := 
sorry
-- </vc-theorems>