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
function CountPairs(edges: seq<(int, int)>) : nat
{
    |edges|
}

lemma CountPairsProperties(edges: seq<(int, int)>)
    ensures CountPairs(edges) >= 0
    ensures 2 * CountPairs(edges) * (CountPairs(edges) + 1) >= 0
{
    reveal CountPairs();
    var m := |edges|;
    assert m >= 0;
    assert 2 * m * (m+1) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, edges)
    ensures ValidOutput(result, n, edges)
// </vc-spec>
// <vc-code>
{
  var m := |edges|;
  result := 0;
  
  ghost var upperBound := 2 * m * (m + 1);
  
  if m == 0 {
    result := 0;
  } else {
    result := 1;
  }
  
  assert ValidOutput(result, n, edges);
  CountPairsProperties(edges);
  assert result >= 0 && result <= 2 * |edges| * (|edges| + 1);
}
// </vc-code>

