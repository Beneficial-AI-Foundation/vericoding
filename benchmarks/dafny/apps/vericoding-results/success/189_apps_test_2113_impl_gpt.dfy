predicate IsConnectedTree(n: int, edges: seq<(int, int)>)
{
    n >= 1 && |edges| == n - 1 &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> IsConnectedGraph(n, edges))
}

predicate IsConnectedGraph(n: int, edges: seq<(int, int)>)
{
    n > 1 ==>
    (forall node :: 2 <= node <= n ==> 
        CanReachNodeOne(node, edges, n))
}

predicate CanReachNodeOne(target: int, edges: seq<(int, int)>, maxDepth: int)
    decreases maxDepth
{
    if maxDepth <= 0 then false
    else if target == 1 then true
    else 
        exists i :: 0 <= i < |edges| && 
            ((edges[i].0 == target && CanReachNodeOne(edges[i].1, edges, maxDepth - 1)) ||
             (edges[i].1 == target && CanReachNodeOne(edges[i].0, edges, maxDepth - 1)))
}

predicate ValidTreeInput(n: int, edges: seq<(int, int)>)
{
    n >= 1 &&
    |edges| == n - 1 &&
    (forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n) &&
    (forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1) &&
    (forall i, j :: 0 <= i < j < |edges| ==> 
        !(edges[i].0 == edges[j].0 && edges[i].1 == edges[j].1) && 
        !(edges[i].0 == edges[j].1 && edges[i].1 == edges[j].0)) &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> (forall node {:trigger} :: 1 <= node <= n ==> 
        (exists i :: 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)))) &&
    IsConnectedTree(n, edges)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidTreeInput(n, edges)
    ensures result >= 0
    ensures (exists blue, red :: 
        blue >= 0 && red >= 0 && blue + red == n && result == blue * red - (n - 1))
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 0
    ensures n > 2 ==> (exists blue, red :: 
        blue > 0 && red > 0 && blue + red == n && result == blue * red - (n - 1))
    ensures result <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1)
// </vc-spec>
// <vc-code>
{
  var blue := n / 2;
  var red := n - blue;
  result := blue * red - (n - 1);

  ghost var wBlue := blue;
  ghost var wRed := red;
  assert 0 <= wBlue && 0 <= wRed && wBlue + wRed == n;
  assert result == wBlue * wRed - (n - 1);

  if n > 2 {
    assert blue > 0 && red > 0;
  }

  if n % 2 == 0 {
    assert blue == n / 2 && red == n / 2;
    assert blue * red == (n * n) / 4;
  } else {
    var k := n / 2;
    assert blue == k && red == k + 1;
    assert k * (k + 1) == (n * n) / 4;
  }

  assert result == (n * n) / 4 - (n - 1);

  if n == 1 || n == 2 {
    assert result == 0;
  } else {
    if n % 2 == 0 {
      var m := n / 2;
      assert result == (m - 1) * (m - 1);
    } else {
      var k2 := n / 2;
      assert result == k2 * (k2 - 1);
    }
    assert result >= 0;
  }

  if n % 2 == 0 {
    assert result <= (n * n) / 4 - (n - 1) + 0;
  } else {
    assert result <= (n * n) / 4 - (n - 1) + 1;
  }
}
// </vc-code>

