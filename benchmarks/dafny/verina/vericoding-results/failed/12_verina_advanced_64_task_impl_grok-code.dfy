// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveElement(lst: seq<nat>, target: nat) returns (result: seq<nat>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i] != target
    ensures
        forall i :: 0 <= i < |result| ==> 
            exists j :: 0 <= j < |lst| && lst[j] == result[i] && lst[j] != target
    ensures
        forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==> 
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
            result[k1] == lst[i] && result[k2] == lst[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): recursive implementation to remove target elements while preserving relative order */
  if |lst| == 0 {
    result := [];
  } else {
    var rest := RemoveElement(lst[1..], target);
    if lst[0] == target {
      result := rest;
    } else {
      result := [lst[0]] + rest;
    }
  }
}
// </vc-code>
