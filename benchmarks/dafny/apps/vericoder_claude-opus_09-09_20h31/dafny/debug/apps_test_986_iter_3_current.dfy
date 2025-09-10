predicate ValidInput(n: int, k: int, requests: seq<int>)
{
    n >= 1 && k >= 1 && |requests| == n &&
    forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
}

predicate ValidSolution(n: int, k: int, requests: seq<int>, cost: int)
{
    ValidInput(n, k, requests) && cost >= 0 && cost <= n
}

// <vc-helpers>
function CountUnique(requests: seq<int>): int
{
    |set i | 0 <= i < |requests| :: requests[i]|
}

lemma CountUniqueBound(requests: seq<int>, n: int)
    requires |requests| == n
    requires forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
    ensures 0 <= CountUnique(requests) <= n
{
    var uniqueSet := set i | 0 <= i < |requests| :: requests[i];
    var rangeSet := set x | 1 <= x <= n;
    
    // Prove that uniqueSet is a subset of rangeSet
    assert forall x :: x in uniqueSet ==> x in rangeSet by {
        forall x | x in uniqueSet
        ensures x in rangeSet
        {
            var j :| 0 <= j < |requests| && requests[j] == x;
            assert 1 <= requests[j] <= n;
            assert 1 <= x <= n;
        }
    }
    
    // Since uniqueSet ⊆ rangeSet and |rangeSet| == n
    assert |rangeSet| == n by {
        assert rangeSet == set x | 1 <= x <= n;
        assert |rangeSet| == n;
    }
    
    // Subset cardinality property
    assert uniqueSet <= rangeSet;
    assert |uniqueSet| <= |rangeSet|;
    assert |uniqueSet| <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, requests: seq<int>) returns (cost: int)
    requires ValidInput(n, k, requests)
    ensures ValidSolution(n, k, requests, cost)
// </vc-spec>
// <vc-code>
{
    var uniqueCount := CountUnique(requests);
    cost := if uniqueCount <= k then uniqueCount else k;
    
    // Prove the postcondition
    CountUniqueBound(requests, n);
    assert 0 <= uniqueCount <= n;
    assert cost <= uniqueCount;
    assert cost <= n;
}
// </vc-code>

