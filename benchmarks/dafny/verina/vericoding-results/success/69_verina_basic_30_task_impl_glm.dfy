// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced comprehension with loop to fix index out-of-range compilation error */
{
  var n := |a|;
  var s: seq<int> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == a[j] % b[j]
  {
    s := s + [a[i] % b[i]];
    i := i + 1;
  }
  result := s;
}
// </vc-code>
