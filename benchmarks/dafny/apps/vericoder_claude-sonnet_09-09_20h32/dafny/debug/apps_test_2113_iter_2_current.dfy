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
lemma MaxProductLemma(n: int)
    requires n >= 1
    ensures forall blue, red :: blue >= 0 && red >= 0 && blue + red == n ==>
        blue * red <= (n / 2) * ((n + 1) / 2)
{
    if n == 1 {
        assert (n / 2) * ((n + 1) / 2) == 0 * 1 == 0;
        forall blue, red | blue >= 0 && red >= 0 && blue + red == n {
            assert (blue == 0 && red == 1) || (blue == 1 && red == 0);
        }
    } else {
        var opt_blue := n / 2;
        var opt_red := (n + 1) / 2;
        assert opt_blue + opt_red == n;
        
        forall blue, red | blue >= 0 && red >= 0 && blue + red == n {
            var diff := blue - opt_blue;
            assert red == opt_red - diff;
            assert blue * red == (opt_blue + diff) * (opt_red - diff);
            assert blue * red == opt_blue * opt_red - diff * diff + diff * (opt_red - opt_blue);
            assert opt_red - opt_blue <= 1;
            if opt_red == opt_blue {
                assert blue * red <= opt_blue * opt_red;
            } else {
                assert opt_red == opt_blue + 1;
                assert blue * red == opt_blue * opt_red + diff - diff * diff;
                assert blue * red <= opt_blue * opt_red;
            }
        }
    }
}

lemma OptimalPartitionExists(n: int)
    requires n >= 1
    ensures exists blue, red :: 
        blue >= 0 && red >= 0 && blue + red == n && 
        blue * red == (n / 2) * ((n + 1) / 2)
{
    var blue := n / 2;
    var red := (n + 1) / 2;
    assert blue + red == n;
    assert blue * red == (n / 2) * ((n + 1) / 2);
}
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
    if n == 1 {
        result := 0;
        assert result == 0 * 1 - 0;
    } else if n == 2 {
        result := 0;
        assert result == 1 * 1 - 1;
    } else {
        var blue := n / 2;
        var red := (n + 1) / 2;
        result := blue * red - (n - 1);
        assert blue > 0 && red > 0;
        assert blue + red == n;
    }
}
// </vc-code>

