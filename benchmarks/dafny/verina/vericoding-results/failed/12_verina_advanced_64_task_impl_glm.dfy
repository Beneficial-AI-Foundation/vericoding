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
  /* code modified by LLM (iteration 5): fixed indentation and invariant issues */
  var newSeq := [];
  for i := 0 to |lst|
      invariant forall k :: 0 <= k < |newSeq| ==> newSeq[k] != target
      invariant forall k :: 0 <= k < |newSeq| ==> exists j :: 0 <= j < i && lst[j] == newSeq[k] && lst[j] != target
      invariant forall a, b :: 0 <= a < b < i && lst[a] != target && lst[b] != target ==> (exists k1, k2 :: 0 <= k1 < k2 < |newSeq| && newSeq[k1] == lst[a] && newSeq[k2] == lst[b])
  {
    if lst[i] != target {
      newSeq := newSeq + [lst[i]];
    }
  }
  result := newSeq;
}
// </vc-code>
