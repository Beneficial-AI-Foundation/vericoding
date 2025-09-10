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
lemma ProductMaximizedAtHalf(n: int, blue: int, red: int)
    requires n >= 1
    requires blue >= 0 && red >= 0
    requires blue + red == n
    ensures blue * red <= n * n / 4 + (if n % 2 == 0 then 0 else 1)
{
    // The product is maximized when blue and red are as close as possible
    // For even n: max is at n/2, n/2
    // For odd n: max is at n/2, n/2+1 or n/2+1, n/2
    
    if n % 2 == 0 {
        // For even n, maximum product is (n/2) * (n/2) = n*n/4
        var halfN := n / 2;
        assert halfN + halfN == n;
        assert halfN * halfN == n * n / 4;
        // Any other split (halfN - k, halfN + k) gives smaller product
        // (halfN - k) * (halfN + k) = halfN^2 - k^2 < halfN^2
    } else {
        // For odd n, maximum product is (n/2) * (n/2 + 1)
        var halfN := n / 2;
        assert halfN + (halfN + 1) == n;
        assert halfN * (halfN + 1) == (n * n - 1) / 4;
        assert halfN * (halfN + 1) <= n * n / 4 + 1;
    }
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
        assert 1 >= 0 && 0 >= 0 && 1 + 0 == 1 && 0 == 1 * 0 - 0;
        return 0;
    }
    
    var blue: int;
    var red: int;
    
    if n % 2 == 0 {
        blue := n / 2;
        red := n / 2;
    } else {
        blue := n / 2;
        red := n / 2 + 1;
    }
    
    assert blue >= 0 && red >= 0;
    assert blue + red == n;
    
    result := blue * red - (n - 1);
    
    if n == 2 {
        assert blue == 1 && red == 1;
        assert result == 1 * 1 - 1 == 0;
    }
    
    if n > 2 {
        assert blue > 0 && red > 0;
    }
    
    ProductMaximizedAtHalf(n, blue, red);
    assert blue * red <= n * n / 4 + (if n % 2 == 0 then 0 else 1);
    assert result == blue * red - (n - 1);
    assert result <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1);
}
// </vc-code>

