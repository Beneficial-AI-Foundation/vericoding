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
  /* code modified by LLM (iteration 5): added invariant to prove index safety */
  result := [];
  ghost var result_indices: seq<nat> := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |result| == |result_indices|
    invariant forall k :: 0 <= k < |result_indices| ==> 0 <= result_indices[k] < |lst|
    invariant forall k :: 0 <= k < |result| ==> result[k] == lst[result_indices[k]]
    invariant forall k :: 0 <= k < |result| ==> result[k] != target
    invariant forall k1, k2 :: 0 <= k1 < k2 < |result_indices| ==> result_indices[k1] < result_indices[k2]
    invariant forall k :: 0 <= k < |result_indices| ==> result_indices[k] < i
    invariant forall j :: 0 <= j < i && lst[j] != target ==> j in result_indices
  {
    if lst[i] != target {
      result := result + [lst[i]];
      result_indices := result_indices + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
