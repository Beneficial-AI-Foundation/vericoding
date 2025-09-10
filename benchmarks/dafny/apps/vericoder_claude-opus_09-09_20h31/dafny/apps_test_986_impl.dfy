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

lemma RangeSetCardinality(n: int)
    requires n >= 1
    ensures |set x | 1 <= x <= n| == n
{
    var rangeSet := set x | 1 <= x <= n;
    var rangeSeq := seq(n, i => i + 1);
    
    assert |rangeSeq| == n;
    assert forall i :: 0 <= i < n ==> rangeSeq[i] == i + 1;
    assert forall i :: 0 <= i < n ==> 1 <= rangeSeq[i] <= n;
    
    // All elements in rangeSeq are distinct
    assert forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> rangeSeq[i] != rangeSeq[j] by {
        forall i, j | 0 <= i < n && 0 <= j < n && i != j
        ensures rangeSeq[i] != rangeSeq[j]
        {
            assert rangeSeq[i] == i + 1;
            assert rangeSeq[j] == j + 1;
            assert i + 1 != j + 1;
        }
    }
    
    // rangeSeq contains all elements from 1 to n
    assert forall x :: 1 <= x <= n ==> exists i :: 0 <= i < n && rangeSeq[i] == x by {
        forall x | 1 <= x <= n
        ensures exists i :: 0 <= i < n && rangeSeq[i] == x
        {
            var i := x - 1;
            assert 0 <= i < n;
            assert rangeSeq[i] == i + 1 == x;
        }
    }
    
    // The set of elements in rangeSeq equals rangeSet
    assert rangeSet == set i | 0 <= i < |rangeSeq| :: rangeSeq[i] by {
        forall x
        ensures x in rangeSet <==> x in (set i | 0 <= i < |rangeSeq| :: rangeSeq[i])
        {
            if x in rangeSet {
                assert 1 <= x <= n;
                var i := x - 1;
                assert 0 <= i < n;
                assert rangeSeq[i] == x;
                assert x in (set i | 0 <= i < |rangeSeq| :: rangeSeq[i]);
            }
            if x in (set i | 0 <= i < |rangeSeq| :: rangeSeq[i]) {
                var i :| 0 <= i < |rangeSeq| && rangeSeq[i] == x;
                assert rangeSeq[i] == i + 1;
                assert x == i + 1;
                assert 1 <= x <= n;
                assert x in rangeSet;
            }
        }
    }
    
    // Since all elements are distinct, the set has the same cardinality as the sequence
    var setFromSeq := set i | 0 <= i < |rangeSeq| :: rangeSeq[i];
    assert |setFromSeq| == |rangeSeq| by {
        // This follows from the fact that all elements in rangeSeq are distinct
        // Dafny can infer this from the distinctness property we proved above
    }
    assert |rangeSet| == |setFromSeq|;
    assert |rangeSet| == n;
}

lemma CountUniqueBound(requests: seq<int>, n: int)
    requires n >= 1
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
            assert x in rangeSet;
        }
    }
    
    // Use the lemma to establish |rangeSet| == n
    RangeSetCardinality(n);
    assert |rangeSet| == n;
    
    // Subset cardinality property - uniqueSet is a subset of rangeSet
    // Therefore |uniqueSet| <= |rangeSet|
    assert |uniqueSet| <= n;
    assert CountUnique(requests) == |uniqueSet|;
    assert 0 <= CountUnique(requests) <= n;
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

