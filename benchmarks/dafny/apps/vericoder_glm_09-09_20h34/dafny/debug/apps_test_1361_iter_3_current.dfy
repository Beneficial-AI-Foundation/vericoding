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

lemma lemma_maxDiff_remove(s: seq<int>, k: int)
    requires ValidInput(s)
    requires 0 < k < |s|
    ensures maxDiff(s[..k] + s[k+1..]) <= maxDiff(s)
    ensures maxDiff(s[..k] + s[k+1..]) < maxDiff(s) ==> 
        maxDiff(s) == s[k+1] - s[k-1] && maxDiff(s[..k] + s[k+1..]) == maxDiff(s[..k+1])
{
    calc {
        maxDiff(s[..k] + s[k+1..]);
    ==  // Definition of maxDiff
        if |s[..k] + s[k+1..]| <= 1 then 0 else
        var maxSoFar := if (s[..k] + s[k+1..])[1] - (s[..k] + s[k+1..])[0] >= 0 
                        then (s[..k] + s[k+1..])[1] - (s[..k] + s[k+1..])[0] else 0;
        maxDiffHelper(s[..k] + s[k+1..], 2, maxSoFar)
    }
    
    if |s| == 3 {
        assert k == 1;
        assert s[..k] + s[k+1..] == [s[0], s[2]];
        assert maxDiff(s) == s[2] - s[0];
        assert maxDiff([s[0], s[2]]) == s[2] - s[0];
    } else {
        var largeDiff := s[k+1] - s[k-1];
        ghost var m := maxDiff(s);
        ghost var m' := maxDiff(s[..k] + s[k+1..]);
        
        calc {
            m;
        ==  // ValidInput implies s[k+1] - s[k-1] > 0
            if |s| <= 1 then 0 else
            var maxSoFar := if s[1] - s[0] >= 0 then s[1] - s[0] else 0;
            maxDiffHelper(s, 2, maxSoFar)
        }
        
        assert m >= largeDiff by {
            if k-1 == 0 && k+1 == 1 {
                assert maxSoFar == s[1] - s[0];
                assert maxDiffHelper(s, 2, maxSoFar) >= maxSoFar == s[1] - s[0];
            }
        }
    }
}

function method solveHelper(holds: seq<int>, k: int): (result: int)
    requires ValidInput(holds)
    requires 1 <= k < |holds| - 1
    ensures result == maxDiff(holds[..k] + holds[k+1..])
{
    maxDiff(holds[..k] + holds[k+1..])
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
    var best := maxDiff(holds[1..]);
    var removeIdx := 1;
    
    var i := 1;
    while i < |holds| - 1
        invariant 1 <= i <= |holds| - 1
        invariant 1 <= removeIdx < |holds| - 1
        invariant best == maxDiff(holds[..removeIdx] + holds[removeIdx+1..])
    {
        var current := solveHelper(holds, i);
        if current < best {
            best := current;
            removeIdx := i;
        }
        i := i + 1;
    }
    
    return best;
}
// </vc-code>

