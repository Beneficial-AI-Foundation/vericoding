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
    assert forall i :: 0 <= i < k-1 ==> removed[i] < removed[i+1];
    assert removed[k-1] < removed[k]; // This is holds[k-1] < holds[k+1]
    assert forall i :: k < i < |removed| - 1 ==> removed[i] < removed[i+1];
    
    // The difference at the junction point is the maximum
    var junctionDiff := removed[k] - removed[k-1];
    assert junctionDiff == holds[k+1] - holds[k-1];
    
    // Since holds is strictly increasing with gaps >= 1, and we removed one element,
    // the junction creates the largest gap
    assert forall i :: 0 <= i < k-1 ==> removed[i+1] - removed[i] == holds[i+1] - holds[i];
    assert forall i :: k < i < |removed| - 1 ==> removed[i+1] - removed[i] == holds[i+2] - holds[i+1];
    
    // The junction difference is larger than any original difference
    assert holds[k+1] - holds[k-1] >= holds[k+1] - holds[k];
    assert holds[k+1] - holds[k-1] >= holds[k] - holds[k-1];
    
    // Calculate maxDiff explicitly
    assert maxDiff(removed) == junctionDiff;
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
        invariant forall j :: 1 <= j < k ==> result <= maxDiff(holds[..j] + holds[j+1..])
        invariant exists j :: 1 <= j < k && result == maxDiff(holds[..j] + holds[j+1..])
    {
        var diff := holds[k+1] - holds[k-1];
        MaxDiffAfterRemoval(holds, k);
        assert diff == maxDiff(holds[..k] + holds[k+1..]);
        
        if diff > result {
            result := diff;
        }
        
        k := k + 1;
    }
}
// </vc-code>

