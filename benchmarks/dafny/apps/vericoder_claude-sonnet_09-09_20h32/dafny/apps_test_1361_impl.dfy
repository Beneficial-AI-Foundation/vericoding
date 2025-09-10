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
lemma ConcatPreservesMaxDiff(s1: seq<int>, s2: seq<int>)
    requires |s1| >= 1 && |s2| >= 1
    ensures |s1 + s2| >= 2
    ensures maxDiff(s1 + s2) >= 0
{
}

lemma MaxDiffMonotonic(s: seq<int>, k: int)
    requires |s| >= 3
    requires 1 <= k < |s| - 1
    ensures |s[..k] + s[k+1..]| >= 2
{
    assert |s[..k]| == k >= 1;
    assert |s[k+1..]| == |s| - k - 1 >= 1;
}

lemma FirstIterationExists(holds: seq<int>)
    requires ValidInput(holds)
    ensures 1 < |holds| - 1
    ensures |holds[..1] + holds[1+1..]| >= 2
{
    assert |holds| >= 3;
    assert 1 <= 1 < |holds| - 1;
    MaxDiffMonotonic(holds, 1);
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
    FirstIterationExists(holds);
    
    var maxResult := 0;
    var bestK := 1;
    
    MaxDiffMonotonic(holds, 1);
    var removed := holds[..1] + holds[1+1..];
    var currentDiff := maxDiff(removed);
    maxResult := currentDiff;
    bestK := 1;
    
    for k := 2 to |holds| - 1
        invariant 2 <= k <= |holds| - 1
        invariant maxResult >= 0
        invariant exists j :: 1 <= j < k && maxResult == maxDiff(holds[..j] + holds[j+1..])
        invariant forall j :: 1 <= j < k ==> maxResult <= maxDiff(holds[..j] + holds[j+1..])
    {
        MaxDiffMonotonic(holds, k);
        removed := holds[..k] + holds[k+1..];
        currentDiff := maxDiff(removed);
        
        if currentDiff < maxResult {
            maxResult := currentDiff;
            bestK := k;
        }
    }
    
    result := maxResult;
}
// </vc-code>

