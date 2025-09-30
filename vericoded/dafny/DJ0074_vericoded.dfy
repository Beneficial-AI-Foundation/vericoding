// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed CollectUnique to maintain uniqueness invariant */
function CollectUnique(arr1: array<int>, arr2: array<int>, idx: int, collected: seq<int>): seq<int>
  requires 0 <= idx <= arr1.Length
  requires forall i, j :: 0 <= i < j < |collected| ==> collected[i] != collected[j]
  reads arr1, arr2
  decreases arr1.Length - idx
  ensures forall x :: x in CollectUnique(arr1, arr2, idx, collected) ==> (x in arr1[..] && x in arr2[..]) || x in collected
  ensures forall i, j :: 0 <= i < j < |CollectUnique(arr1, arr2, idx, collected)| ==> CollectUnique(arr1, arr2, idx, collected)[i] != CollectUnique(arr1, arr2, idx, collected)[j]
{
  if idx == arr1.Length then
    collected
  else if arr1[idx] in arr2[..] && arr1[idx] !in collected then
    CollectUnique(arr1, arr2, idx + 1, collected + [arr1[idx]])
  else
    CollectUnique(arr1, arr2, idx + 1, collected)
}
// </vc-helpers>

// <vc-spec>
method intersection(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    ensures
        forall i :: 0 <= i < result.Length ==> (result[i] in arr1[..] && result[i] in arr2[..])
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Simplified implementation using CollectUnique function */
{
  var tempSeq := CollectUnique(arr1, arr2, 0, []);
  result := new int[|tempSeq|];
  var i := 0;
  while i < |tempSeq|
    invariant 0 <= i <= |tempSeq|
    invariant |tempSeq| == result.Length
    invariant forall j :: 0 <= j < i ==> result[j] == tempSeq[j]
    invariant forall x :: x in tempSeq ==> x in arr1[..] && x in arr2[..]
    invariant forall p, q :: 0 <= p < q < |tempSeq| ==> tempSeq[p] != tempSeq[q]
  {
    result[i] := tempSeq[i];
    i := i + 1;
  }
}
// </vc-code>
