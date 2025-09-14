

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
// </vc-spec>
// <vc-code>
{
  var result_arr: array<int> := new int[|a|];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> result_arr[j] == a[j] / b[j]
  {
    if i < |a| {
      result_arr[i] := a[i] / b[i];
    }
  }
  return result_arr[..];
}
// </vc-code>

