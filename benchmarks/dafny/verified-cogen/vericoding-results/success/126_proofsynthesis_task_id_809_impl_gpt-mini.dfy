// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate SeqAllGreater(s1: seq<int>, s2: seq<int>) { |s1| == |s2| && (forall i :: 0 <= i < |s1| ==> s1[i] > s2[i]) }
// </vc-helpers>

// <vc-spec>
method IsSmaller(arr1: array<int>, arr2: array<int>) returns (result: bool)
    requires arr1.Length == arr2.Length
    ensures result == (forall i :: 0 <= i < arr1.Length ==> arr1[i] > arr2[i])
// </vc-spec>
// <vc-code>
{
  var n := arr1.Length;
  var i := 0;
  result := true;
  while i < n
    invariant 0 <= i <= n
    invariant result == (forall j :: 0 <= j < i ==> arr1[j] > arr2[j])
  {
    if !(arr1[i] > arr2[i]) {
      result := false;
      i := n;
    } else {
      i := i + 1;
    }
  }
}
// </vc-code>
