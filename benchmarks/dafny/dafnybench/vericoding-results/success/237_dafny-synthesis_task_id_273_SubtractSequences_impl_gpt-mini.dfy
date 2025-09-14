

// <vc-helpers>
// helper code not required
// </vc-helpers>

// <vc-spec>
method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall j :: 0 <= j < i ==> arr[j] == a[j] - b[j]
  {
    arr[i] := a[i] - b[i];
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>

