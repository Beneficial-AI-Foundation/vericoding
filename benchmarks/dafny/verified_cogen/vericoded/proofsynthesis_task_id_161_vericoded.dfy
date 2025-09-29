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
    invariant forall j :: 0 <= j < |result| ==> (result[j] in arr1[..] && !(result[j] in arr2[..]))
    invariant forall j :: 0 <= j < i ==> (arr1[j] in arr2[..] || arr1[j] in result)
  {
    var found := false;
    var k := 0;
    while k < arr2.Length
      invariant 0 <= k <= arr2.Length
      invariant found <==> exists m :: 0 <= m < k && arr2[m] == arr1[i]
    {
      if arr2[k] == arr1[i] {
        found := true;
      }
      k := k + 1;
    }
    if !found {
      result := result + [arr1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
