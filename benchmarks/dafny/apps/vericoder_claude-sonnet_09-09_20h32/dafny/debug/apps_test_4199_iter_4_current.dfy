predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>
lemma CountEligibleBounds(heights: seq<int>, k: int)
    ensures 0 <= CountEligible(heights, k) <= |heights|
{
    var eligibleSet := set i | 0 <= i < |heights| && heights[i] >= k :: i;
    var allIndices := set i | 0 <= i < |heights| :: i;
    
    assert forall i :: i in eligibleSet ==> (0 <= i < |heights| && heights[i] >= k);
    assert forall i :: i in eligibleSet ==> 0 <= i < |heights|;
    assert forall i :: i in eligibleSet ==> i in allIndices;
    assert eligibleSet <= allIndices;
    
    // Establish bijection between allIndices and range 0..|heights|
    assert forall i :: 0 <= i < |heights| ==> i in allIndices;
    assert forall i :: i in allIndices ==> 0 <= i < |heights|;
    assert allIndices == set i | 0 <= i < |heights| :: i;
    
    // The cardinality follows from the bijection
    CardinalityOfRange(|heights|);
    assert |allIndices| == |heights|;
    assert |eligibleSet| <= |allIndices|;
    assert |eligibleSet| <= |heights|;
    assert 0 <= |eligibleSet|;
}

lemma CardinalityOfRange(n: int)
    requires n >= 0
    ensures |set i | 0 <= i < n :: i| == n
{
    if n == 0 {
        var emptySet := set i | 0 <= i < 0 :: i;
        assert emptySet == {};
    } else {
        var s := set i | 0 <= i < n :: i;
        var s_prev := set i | 0 <= i < n-1 :: i;
        assert s == s_prev + {n-1};
        assert (n-1) !in s_prev;
        CardinalityOfRange(n-1);
        assert |s| == |s_prev| + 1 == (n-1) + 1 == n;
    }
}

lemma CountEligibleEmpty(k: int)
    ensures CountEligible([], k) == 0
{
    var emptySet := set i | 0 <= i < 0 && [][i] >= k :: i;
    assert emptySet == {};
}

lemma CountEligibleStep(heights: seq<int>, k: int, i: int)
    requires 0 <= i < |heights|
    ensures CountEligible(heights[..i+1], k) == 
            CountEligible(heights[..i], k) + (if heights[i] >= k then 1 else 0)
{
    var prefixSet := set j | 0 <= j < i && heights[..i][j] >= k :: j;
    var fullSet := set j | 0 <= j < i+1 && heights[..i+1][j] >= k :: j;
    
    assert heights[..i+1][i] == heights[i];
    assert forall j :: 0 <= j < i ==> heights[..i+1][j] == heights[..i][j];
    
    if heights[i] >= k {
        assert i in fullSet;
        assert i !in prefixSet;
        assert fullSet == prefixSet + {i};
        assert |fullSet| == |prefixSet| + 1;
        assert CountEligible(heights[..i+1], k) == CountEligible(heights[..i], k) + 1;
    } else {
        assert i !in fullSet;
        assert fullSet == prefixSet;
        assert |fullSet| == |prefixSet|;
        assert CountEligible(heights[..i+1], k) == CountEligible(heights[..i], k);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
{
    CountEligibleBounds(heights, k);
    count := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= count <= i
        invariant count == CountEligible(heights[..i], k)
    {
        CountEligibleStep(heights, k, i);
        if heights[i] >= k {
            count := count + 1;
        }
        i := i + 1;
    }
    
    assert i == n;
    assert heights[..n] == heights;
    assert count == CountEligible(heights[..n], k);
    assert count == CountEligible(heights, k);
}
// </vc-code>

