// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqContains(s: seq<int>, x: int): bool { x in s }
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
    invariant forall k :: 0 <= k < |result| ==> result[k] in arr1[..] && !(result[k] in arr2[..])
    invariant forall j :: 0 <= j < i ==> (arr1[j] in arr2[..] || arr1[j] in result)
    decreases arr1.Length - i
  {
    var x := arr1[i];
    if !(x in arr2[..]) {
      result := result + [x];
    }

    i := i + 1;
  }
}

// </vc-code>
