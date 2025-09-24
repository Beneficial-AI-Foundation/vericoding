-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum_sum_with_deletion (arr : List Int) : Int :=
  sorry

def list_maximum (arr : List Int) : Int :=
  sorry

def list_sum (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_scaling {arr : List Int} {scale : Int}
  (h : arr ≠ []) (hs : scale > 0) :
  maximum_sum_with_deletion (List.map (· * scale) arr) =
  maximum_sum_with_deletion arr * scale :=
sorry
-- </vc-theorems>