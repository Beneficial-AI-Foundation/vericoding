// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple pointwise product accessor for a given index */
function productAt(a: seq<int>, b: seq<int>, i: int): int
  requires 0 <= i < |a| && |a| == |b|
{
  a[i] * b[i]
}
// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced invalid sequence comprehension with a verified loop using sequence updates */
  var n := |a|;
  result := a;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == n
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] * b[j]
    invariant forall j :: i <= j < n ==> result[j] == a[j]
  {
    result := result[i := productAt(a, b, i)];
    i := i + 1;
  }
}
// </vc-code>
