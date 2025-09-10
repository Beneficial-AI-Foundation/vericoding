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
    assert |removed| >= 2;
    
    // The sequence after removal is still sorted
    assert forall i :: 0 <= i < |removed| - 1 ==> removed[i] < removed[i + 1];
    
    // The new difference at position k-1 is holds[k+1] - holds[k-1]
    assert removed[k-1] == holds[k-1];
    assert removed[k] == holds[k+1];
    
    // Since the sequence is strictly increasing, this is the maximum difference
    assert forall i :: 0 <= i < |removed| - 1 ==> removed[i+1] - removed[i] >= 1;
    assert removed[k] - removed[k-1] == holds[k+1] - holds[k-1];
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
    result := 0;
    var k := 1;
    
    while k < |holds| - 1
        invariant 1 <= k <= |holds| - 1
        invariant result >= 0
        invariant forall j :: 1 <= j < k ==> result <= maxDiff(holds[..j] + holds[j+1..])
        invariant exists j :: 1 <= j < k && result == maxDiff(holds[..j] + holds[j+1..]) || (k == 1 && result == 0)
    {
        var diff := holds[k+1] - holds[k-1];
        MaxDiffAfterRemoval(holds, k);
        
        if diff > result {
            result := diff;
        }
        
        k := k + 1;
    }
}
// </vc-code>

