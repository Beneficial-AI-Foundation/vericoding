// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
predicate ValidIndexRange(s: seq<int>, i: int) { 0 <= i < |s| }
lemma ConcatLemma(a: seq<int>, b: seq<int>, k: int) 
  requires 0 <= k < |a| + |b|
  ensures if k < |a| then (a + b)[k] == a[k] else (a + b)[k] == b[k - |a|]
  {
    if k < |a| {
      assert (a + b)[k] == a[k];
    } else {
      assert (a + b)[k] == b[k - |a|];
    }
  }
// </vc-helpers>

// <vc-spec>
method Concat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures |result| == |a| + |b|
    ensures forall k :: 0 <= k < |a| ==> result[k] == a[k]
    ensures forall k :: 0 <= k < |b| ==> result[k + |a|] == b[k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed array/seq assignment errors and implemented proper sequence concatenation */
{
  result := a + b;
}
// </vc-code>
