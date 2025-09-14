// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall k :: 0 <= k < |result| ==> (result[k] in arr1[..i] && !(result[k] in arr2[..]))
    invariant forall k :: 0 <= k < i ==> (arr1[k] in arr2[..] || arr1[k] in result)
  {
    if !(arr1[i] in arr2[..]) {
      result := result + [arr1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
