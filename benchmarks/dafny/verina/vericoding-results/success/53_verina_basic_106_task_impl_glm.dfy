// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced sequence comprehension with while-loop for better verification */
  var n := |a|;
  var i := 0;
  var s := [];
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == a[j] + b[j]
  {
    s := s + [a[i] + b[i]];
    i := i + 1;
  }
  result := s;
}
// </vc-code>
