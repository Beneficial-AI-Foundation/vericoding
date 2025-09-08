Given n holds at increasing heights, remove exactly one hold (not the first or last) 
to minimize the track difficulty. The difficulty is the maximum difference between 
consecutive hold heights.

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

method solve(holds: seq<int>) returns (result: int)
    requires ValidInput(holds)
    ensures result >= 0
    ensures exists k :: 1 <= k < |holds| - 1 && result == maxDiff(holds[..k] + holds[k+1..])
    ensures forall k :: 1 <= k < |holds| - 1 ==> result <= maxDiff(holds[..k] + holds[k+1..])
{
    var i := 1;
    var newSeq := holds[..i] + holds[i+1..];
    result := maxDiff(newSeq);
    i := i + 1;

    while i < |holds| - 1
        invariant 1 < i <= |holds| - 1
        invariant result >= 0
        invariant forall k :: 1 <= k < i ==> result <= maxDiff(holds[..k] + holds[k+1..])
        invariant exists k :: 1 <= k < i && result == maxDiff(holds[..k] + holds[k+1..])
    {
        newSeq := holds[..i] + holds[i+1..];
        var diff := maxDiff(newSeq);
        if diff < result {
            result := diff;
        }
        i := i + 1;
    }
}
