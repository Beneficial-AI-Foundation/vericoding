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
  /* code modified by LLM (iteration 5): fixed invariant to properly handle existence of indices in result */
  result := [];
  ghost var mapping := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |mapping| == |result|
    invariant forall k :: 0 <= k < |result| ==> result[k] != target
    invariant forall k :: 0 <= k < |result| ==> 0 <= mapping[k] < i && lst[mapping[k]] == result[k] && lst[mapping[k]] != target
    invariant forall k1, k2 :: 0 <= k1 < k2 < |result| ==> mapping[k1] < mapping[k2]
    invariant forall p, q :: 0 <= p < q < i && lst[p] != target && lst[q] != target ==> 
      (exists idx_p, idx_q :: 0 <= idx_p < |result| && 0 <= idx_q < |result| && 
        mapping[idx_p] == p && mapping[idx_q] == q && idx_p < idx_q)
  {
    if lst[i] != target {
      result := result + [lst[i]];
      mapping := mapping + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
