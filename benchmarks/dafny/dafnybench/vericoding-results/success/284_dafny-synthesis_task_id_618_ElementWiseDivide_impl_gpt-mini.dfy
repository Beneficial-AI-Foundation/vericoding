

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
  var r: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == a[j] / b[j]
    decreases |a| - i
  {
    r := r + [a[i] / b[i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

