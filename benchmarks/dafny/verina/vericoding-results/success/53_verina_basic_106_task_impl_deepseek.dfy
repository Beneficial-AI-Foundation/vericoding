// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumElements(index: int, a: seq<int>, b: seq<int>): int requires 0 <= index < |a| && |a| == |b| { a[index] + b[index] }

lemma SumElementsLemma(a: seq<int>, b: seq<int>, i: int)
  requires |a| == |b| && 0 <= i < |a|
  ensures SumElements(i, a, b) == a[i] + b[i]
{
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added bounds check to seq comprehension */
  result := seq(|a|, i requires 0 <= i < |a| => SumElements(i, a, b));
  
  // Proof of ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
  var k: int := 0;
  while k < |a|
    invariant 0 <= k <= |a|
    invariant forall j :: 0 <= j < k ==> result[j] == a[j] + b[j]
  {
    // result[k] = a[k] + b[k] by construction
    assert result[k] == SumElements(k, a, b);
    SumElementsLemma(a, b, k);
    assert result[k] == a[k] + b[k];
    k := k + 1;
  }
}
// </vc-code>
