predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < n ==> a[i] >= 0
}

function CountSurvivors(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    CountSurvivorsFrom(n, a, 0, n)
}

function CountSurvivorsFrom(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
}

// <vc-helpers>
lemma CountSurvivorsFromUnroll(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start < n
    requires left <= n
    ensures CountSurvivorsFrom(n, a, start, left) == 
            (if n - 1 - start < left then 1 else 0) + 
            CountSurvivorsFrom(n, a, start + 1, if n - 1 - start - a[n - 1 - start] < left then n - 1 - start - a[n - 1 - start] else left)
{
    // This follows directly from the definition of CountSurvivorsFrom
}

lemma CountSurvivorsFromBound(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    ensures CountSurvivorsFrom(n, a, start, left) <= n - start
    decreases n - start
{
    if start >= n {
        assert CountSurvivorsFrom(n, a, start, left) == 0;
        assert 0 <= n - start;
    } else {
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        
        CountSurvivorsFromBound(n, a, start + 1, newLeft);
        assert CountSurvivorsFrom(n, a, start + 1, newLeft) <= n - (start + 1);
        
        assert survives <= 1;
        assert CountSurvivorsFrom(n, a, start, left) == survives + CountSurvivorsFrom(n, a, start + 1, newLeft);
        assert CountSurvivorsFrom(n, a, start, left) <= 1 + (n - start - 1);
        assert CountSurvivorsFrom(n, a, start, left) <= n - start;
    }
}

lemma IterativeCountBound(n: int, a: seq<int>, k: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= k <= n
    requires left <= n
    ensures IterativeCount(n, a, k, left) <= k
    decreases k
{
    if k == 0 {
        assert IterativeCount(n, a, k, left) == 0;
    } else {
        var i := k - 1;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        
        IterativeCountBound(n, a, k - 1, newLeft);
        assert IterativeCount(n, a, k - 1, newLeft) <= k - 1;
        
        assert survives <= 1;
        assert IterativeCount(n, a, k, left) == survives + IterativeCount(n, a, k - 1, newLeft);
        assert IterativeCount(n, a, k, left) <= 1 + (k - 1);
        assert IterativeCount(n, a, k, left) <= k;
    }
}

lemma CountSurvivorsCorrespondence(n: int, a: seq<int>, k: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= k <= n
    requires left <= n
    ensures CountSurvivorsFrom(n, a, n - k, left) == IterativeCount(n, a, k, left)
    decreases k
{
    if k == 0 {
        assert CountSurvivorsFrom(n, a, n, left) == 0;
        assert IterativeCount(n, a, 0, left) == 0;
    } else {
        var start := n - k;
        var i := n - 1 - start;
        assert i == k - 1;
        
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        
        CountSurvivorsFromUnroll(n, a, start, left);
        assert CountSurvivorsFrom(n, a, start, left) == survives + CountSurvivorsFrom(n, a, start + 1, newLeft);
        
        CountSurvivorsCorrespondence(n, a, k - 1, newLeft);
        assert CountSurvivorsFrom(n, a, start + 1, newLeft) == IterativeCount(n, a, k - 1, newLeft);
        
        assert IterativeCount(n, a, k, left) == survives + IterativeCount(n, a, k - 1, newLeft);
    }
}

function IterativeCount(n: int, a: seq<int>, k: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= k <= n
    requires left <= n
    decreases k
{
    if k == 0 then 0
    else
        var i := k - 1;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + IterativeCount(n, a, k - 1, newLeft)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result <= n
    ensures result == CountSurvivors(n, a)
// </vc-spec>
// <vc-code>
{
    var left := n;
    var count := 0;
    var k := n;
    
    while k > 0
        invariant 0 <= k <= n
        invariant left <= n
        invariant count >= 0
        invariant count <= n - k
        invariant count + IterativeCount(n, a, k, left) == IterativeCount(n, a, n, n)
    {
        var i := k - 1;
        if i < left {
            count := count + 1;
        }
        
        if i - a[i] < left {
            left := i - a[i];
        }
        
        k := k - 1;
    }
    
    assert k == 0;
    assert count <= n;
    assert IterativeCount(n, a, 0, left) == 0;
    assert count == IterativeCount(n, a, n, n);
    
    IterativeCountBound(n, a, n, n);
    assert IterativeCount(n, a, n, n) <= n;
    
    CountSurvivorsCorrespondence(n, a, n, n);
    assert IterativeCount(n, a, n, n) == CountSurvivorsFrom(n, a, 0, n);
    assert CountSurvivorsFrom(n, a, 0, n) == CountSurvivors(n, a);
    
    result := count;
}
// </vc-code>

