predicate ValidInput(testCases: seq<(int, int, seq<(int, int)>)>)
{
    |testCases| >= 0 &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        n >= 1 && 1 <= x <= n && |operations| >= 0 &&
        (forall j :: 0 <= j < |operations| ==> 
            var (l, r) := operations[j];
            1 <= l <= r <= n)
}

function computeFinalBounds(x: int, operations: seq<(int, int)>): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
{
    computeFinalBoundsHelper(x, x, operations, 0)
}

predicate ValidResults(testCases: seq<(int, int, seq<(int, int)>)>, results: seq<int>)
    requires ValidInput(testCases)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        var finalBounds := computeFinalBounds(x, operations);
        results[i] == finalBounds.1 - finalBounds.0 + 1 &&
        finalBounds.0 <= x <= finalBounds.1 &&
        results[i] >= 1 &&
        1 <= finalBounds.0 <= finalBounds.1 <= n
}

// <vc-helpers>
function computeFinalBoundsHelper(minBound: int, maxBound: int, operations: seq<(int, int)>, index: int): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    requires 0 <= index <= |operations|
    decreases |operations| - index
{
    if index >= |operations| then
        (minBound, maxBound)
    else
        var (l, r) := operations[index];
        var newMinBound := if minBound < l then l else minBound;
        var newMaxBound := if maxBound > r then r else maxBound;
        computeFinalBoundsHelper(newMinBound, newMaxBound, operations, index + 1)
}

lemma computeFinalBoundsProperties(x: int, operations: seq<(int, int)>)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    ensures var (minB, maxB) := computeFinalBounds(x, operations);
            minB <= x <= maxB
{
    computeFinalBoundsHelperProperties(x, x, operations, 0, x);
}

lemma computeFinalBoundsHelperProperties(minBound: int, maxBound: int, operations: seq<(int, int)>, index: int, x: int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    requires 0 <= index <= |operations|
    requires minBound <= x <= maxBound
    ensures var (minB, maxB) := computeFinalBoundsHelper(minBound, maxBound, operations, index);
            minB <= x <= maxB && minB <= maxB
    decreases |operations| - index
{
    if index >= |operations| {
        // Base case
    } else {
        var (l, r) := operations[index];
        var newMinBound := if minBound < l then l else minBound;
        var newMaxBound := if maxBound > r then r else maxBound;
        
        assert newMinBound <= x <= newMaxBound;
        computeFinalBoundsHelperProperties(newMinBound, newMaxBound, operations, index + 1, x);
    }
}

lemma computeFinalBoundsInRange(n: int, x: int, operations: seq<(int, int)>)
    requires n >= 1 && 1 <= x <= n
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        1 <= l <= r <= n
    ensures var (minB, maxB) := computeFinalBounds(x, operations);
            1 <= minB <= maxB <= n
{
    computeFinalBoundsHelperInRange(x, x, operations, 0, n);
}

lemma computeFinalBoundsHelperInRange(minBound: int, maxBound: int, operations: seq<(int, int)>, index: int, n: int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        1 <= l <= r <= n
    requires 0 <= index <= |operations|
    requires 1 <= minBound <= maxBound <= n
    ensures var (minB, maxB) := computeFinalBoundsHelper(minBound, maxBound, operations, index);
            1 <= minB <= maxB <= n
    decreases |operations| - index
{
    if index >= |operations| {
        // Base case
    } else {
        var (l, r) := operations[index];
        var newMinBound := if minBound < l then l else minBound;
        var newMaxBound := if maxBound > r then r else maxBound;
        
        assert 1 <= newMinBound <= newMaxBound <= n;
        computeFinalBoundsHelperInRange(newMinBound, newMaxBound, operations, index + 1, n);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    
    for i := 0 to |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant forall k :: 0 <= k < i ==> 
            var (n, x, operations) := testCases[k];
            var finalBounds := computeFinalBounds(x, operations);
            results[k] == finalBounds.1 - finalBounds.0 + 1 &&
            finalBounds.0 <= x <= finalBounds.1 &&
            results[k] >= 1 &&
            1 <= finalBounds.0 <= finalBounds.1 <= n
    {
        var (n, x, operations) := testCases[i];
        var finalBounds := computeFinalBounds(x, operations);
        var result := finalBounds.1 - finalBounds.0 + 1;
        
        computeFinalBoundsProperties(x, operations);
        computeFinalBoundsInRange(n, x, operations);
        
        results := results + [result];
    }
}
// </vc-code>

