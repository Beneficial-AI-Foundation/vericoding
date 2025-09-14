

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == a[j] - b[j]
  {
    s := s + [a[i] - b[i]];
    i := i + 1;
  }
  result := s;
}
// </vc-code>

