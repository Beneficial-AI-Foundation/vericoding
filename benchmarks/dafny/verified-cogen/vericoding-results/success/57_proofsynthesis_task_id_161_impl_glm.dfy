// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added helper function to check element in sequence */
function Contains(s: seq<int>, x: int): bool {
  exists k: int :: 0 <= k < |s| && s[k] == x
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(arr1: array<int>, arr2: array<int>) returns (result: seq<int>)
    ensures
        forall i: int ::
            0 <= i < |result| ==> (result[i] in arr1[..] && !(result[i] in arr2[..]))
    ensures
        forall i: int ::
            0 <= i < arr1.Length ==> (arr1[i] in arr2[..] || arr1[i] in result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed parse error by using block for if body */
  var arr2Seq := arr2[..];
  var i := 0;
  result := [];
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j: int :: 0 <= j < i ==> (arr1[j] in arr2Seq || arr1[j] in result)
    invariant forall k: int :: 0 <= k < |result| ==> (result[k] in arr1[..] && !(result[k] in arr2Seq))
  {
    if !Contains(arr2Seq, arr1[i])
    {
      result := result + [arr1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
