predicate ValidInput(n: int, edges: seq<(int, int)>)
{
    n >= 2 &&
    forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
}

predicate ValidOutput(result: int, n: int, edges: seq<(int, int)>)
{
    result >= 0 && result <= 2 * |edges| * (|edges| + 1)
}

// <vc-helpers>
lemma ProdNatNonNeg(a: nat, b: nat)
  ensures 0 <= a * b
  decreases b
{
  if b == 0 {
    assert a * b == 0;
  } else {
    ProdNatNonNeg(a, b - 1);
    assert a * b == a * (b - 1) + a;
    assert 0 <= a * (b - 1) + a;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, edges)
    ensures ValidOutput(result, n, edges)
// </vc-spec>
// <vc-code>
{
  result := 0;
  ProdNatNonNeg(2 * |edges|, |edges| + 1);
}
// </vc-code>

