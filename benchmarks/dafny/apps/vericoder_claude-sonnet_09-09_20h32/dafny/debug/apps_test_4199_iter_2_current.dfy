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
    var allIndices := set i {:trigger} | 0 <= i < |heights| :: i;
    
    assert forall i :: i in eligibleSet ==> 0 <= i < |heights|;
    assert eligibleSet <= allIndices;
    
    // Prove that allIndices has the same cardinality as |heights|
    assert forall i :: 0 <= i < |heights| ==> i in allIndices;
    assert forall i :: i in allIndices ==> 0 <= i < |heights|;
    assert |allIndices| == |heights|;
    
    assert |eligibleSet| <= |allIndices|;
}

lemma CountEligibleEmpty(k: int)
    ensures CountEligible([], k) == 0
{
}

lemma CountEligibleStep(heights: seq<int>, k: int, i: int)
    requires 0 <= i < |heights|
    ensures CountEligible(heights[..i+1], k) == 
            CountEligible(heights[..i], k) + (if heights[i] >= k then 1 else 0)
{
    var prefixSet := set j | 0 <= j < i && heights[j] >= k :: j;
    var fullSet := set j | 0 <= j < i+1 && heights[j] >= k :: j;
    
    if heights[i] >= k {
        assert fullSet == prefixSet + {i};
        assert i !in prefixSet;
        assert |fullSet| == |prefixSet| + 1;
    } else {
        assert fullSet == prefixSet;
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

