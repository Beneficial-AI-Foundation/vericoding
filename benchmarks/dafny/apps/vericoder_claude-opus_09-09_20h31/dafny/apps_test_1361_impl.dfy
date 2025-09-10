predicate ValidInput(holds: seq<int>) {
    |holds| >= 3 && forall i :: 0 <= i < |holds| - 1 ==> holds[i] < holds[i + 1]
}

function maxDiff(s: seq<int>): int
    requires |s| >= 2
    ensures maxDiff(s) >= 0
{
    if |s| <= 1 then 0
    else
        var maxSoFar := if s[1] - s[0] >= 0 then s[1] - s[0] else 0;
        maxDiffHelper(s, 2, maxSoFar)
}

function maxDiffHelper(s: seq<int>, index: int, currentMax: int): int
    requires 1 <= index <= |s|
    requires currentMax >= 0
    ensures maxDiffHelper(s, index, currentMax) >= currentMax
    decreases |s| - index
{
    if index >= |s| then currentMax
    else
        var diff := s[index] - s[index - 1];
        var newMax := if diff > currentMax then diff else currentMax;
        maxDiffHelper(s, index + 1, newMax)
}

// <vc-helpers>
lemma MaxDiffAfterRemoval(holds: seq<int>, k: int)
    requires ValidInput(holds)
    requires 1 <= k < |holds| - 1
    ensures maxDiff(holds[..k] + holds[k+1..]) == holds[k+1] - holds[k-1]
{
    var removed := holds[..k] + holds[k+1..];
    assert |removed| == |holds| - 1;
    assert |removed| >= 2;
    
    // Prove the sequence after removal is still sorted
    assert forall i :: 0 <= i < k-1 ==> removed[i] == holds[i];
    assert removed[k-1] == holds[k-1];
    assert removed[k] == holds[k+1];
    assert forall i :: k < i < |removed| ==> removed[i] == holds[i+1];
    
    // Since holds is strictly increasing, removed is also strictly increasing
    assert forall i :: 0 <= i < k-1 ==> removed[i] < removed[i+1] by {
        forall i | 0 <= i < k-1 
        ensures removed[i] < removed[i+1]
        {
            assert removed[i] == holds[i] && removed[i+1] == holds[i+1];
        }
    }
    
    // Key: holds[k-1] < holds[k] < holds[k+1] because holds is strictly increasing
    assert holds[k-1] < holds[k] < holds[k+1];
    assert removed[k-1] == holds[k-1] && removed[k] == holds[k+1];
    assert removed[k-1] < removed[k];
    
    assert forall i :: k < i < |removed| - 1 ==> removed[i] < removed[i+1] by {
        forall i | k < i < |removed| - 1
        ensures removed[i] < removed[i+1]
        {
            assert removed[i] == holds[i+1] && removed[i+1] == holds[i+2];
        }
    }
    
    // The difference at the junction point
    var junctionDiff := removed[k] - removed[k-1];
    assert junctionDiff == holds[k+1] - holds[k-1];
    
    // Prove that junctionDiff is the maximum difference
    // For indices before k-1
    assert forall i :: 0 <= i < k-1 ==> removed[i+1] - removed[i] <= junctionDiff by {
        forall i | 0 <= i < k-1
        ensures removed[i+1] - removed[i] <= junctionDiff
        {
            assert removed[i+1] - removed[i] == holds[i+1] - holds[i];
            // holds[i+1] - holds[i] < holds[k+1] - holds[k-1] because:
            // holds[i+1] <= holds[k-1] and holds[i] < holds[k-1] < holds[k+1]
            assert holds[i+1] <= holds[k-1];
            assert holds[k-1] < holds[k+1];
            assert holds[i+1] - holds[i] < holds[k+1] - holds[k-1];
        }
    }
    
    // For indices after k
    assert forall i :: k < i < |removed| - 1 ==> removed[i+1] - removed[i] <= junctionDiff by {
        forall i | k < i < |removed| - 1
        ensures removed[i+1] - removed[i] <= junctionDiff
        {
            assert removed[i+1] - removed[i] == holds[i+2] - holds[i+1];
            // holds[i+2] - holds[i+1] < holds[k+1] - holds[k-1] because:
            // holds[k+1] <= holds[i+1] and holds[k-1] < holds[k+1] < holds[i+2]
            assert holds[k+1] <= holds[i+1];
            assert holds[k-1] < holds[k];
            assert holds[i+2] - holds[i+1] < holds[i+2] - holds[k-1];
            assert holds[i+2] - holds[k-1] >= holds[k+1] - holds[k-1];
        }
    }
    
    // Compute maxDiff step by step
    MaxDiffIsJunctionDiff(removed, k, junctionDiff);
}

lemma MaxDiffIsJunctionDiff(s: seq<int>, k: int, junctionDiff: int)
    requires |s| >= 2
    requires 1 <= k < |s|
    requires junctionDiff == s[k] - s[k-1]
    requires forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
    requires forall i :: 0 <= i < k-1 ==> s[i+1] - s[i] <= junctionDiff
    requires forall i :: k < i < |s| - 1 ==> s[i+1] - s[i] <= junctionDiff
    ensures maxDiff(s) == junctionDiff
{
    // maxDiff will find the maximum difference, which is at position k
    assert maxDiff(s) >= junctionDiff;
    
    // Prove that no other difference is larger
    var m := maxDiff(s);
    assert m >= s[k] - s[k-1] == junctionDiff;
    
    // By the definition of maxDiff and our preconditions
    assert forall i :: 0 <= i < |s| - 1 ==> s[i+1] - s[i] <= junctionDiff;
    assert m <= junctionDiff;
    
    assert m == junctionDiff;
}
// </vc-helpers>

// <vc-spec>
method solve(holds: seq<int>) returns (result: int)
    requires ValidInput(holds)
    ensures result >= 0
    ensures exists k :: 1 <= k < |holds| - 1 && result == maxDiff(holds[..k] + holds[k+1..])
    ensures forall k :: 1 <= k < |holds| - 1 ==> result <= maxDiff(holds[..k] + holds[k+1..])
// </vc-spec>
// <vc-code>
{
    result := holds[2] - holds[0];
    MaxDiffAfterRemoval(holds, 1);
    assert result == maxDiff(holds[..1] + holds[2..]);
    
    var k := 2;
    
    while k < |holds| - 1
        invariant 2 <= k <= |holds| - 1
        invariant result >= 0
        invariant forall j :: 1 <= j < k ==> result <= holds[j+1] - holds[j-1]
        invariant forall j :: 1 <= j < k ==> maxDiff(holds[..j] + holds[j+1..]) == holds[j+1] - holds[j-1]
        invariant exists j :: 1 <= j < k && result == holds[j+1] - holds[j-1]
    {
        var diff := holds[k+1] - holds[k-1];
        MaxDiffAfterRemoval(holds, k);
        assert diff == maxDiff(holds[..k] + holds[k+1..]);
        
        if diff > result {
            result := diff;
        }
        
        k := k + 1;
    }
    
    assert forall j :: 1 <= j < |holds| - 1 ==> result <= holds[j+1] - holds[j-1];
    assert forall j :: 1 <= j < |holds| - 1 ==> maxDiff(holds[..j] + holds[j+1..]) == holds[j+1] - holds[j-1];
    assert exists j :: 1 <= j < |holds| - 1 && result == holds[j+1] - holds[j-1];
}
// </vc-code>

