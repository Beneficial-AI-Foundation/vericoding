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
function computeFinalBoundsHelper(low: int, high: int, operations: seq<(int, int)>, index: int): (int, int)
    requires 0 <= index <= |operations|
    requires low <= high
    ensures computeFinalBoundsHelper(low, high, operations, index).0 <= computeFinalBoundsHelper(low, high, operations, index).1
{
    if index == |operations| then (low, high)
    else
        var (l, r) := operations[index];
        var newLow := if l < low then l else low;
        var newHigh := if r > high then r else high;
        computeFinalBoundsHelper(newLow, newHigh, operations, index + 1)
}

lemma FinalBoundsInBounds(n: int, x: int, operations: seq<(int, int)>)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        1 <= l <= r <= n
    requires 1 <= x <= n
    ensures 1 <= computeFinalBounds(x, operations).0 <= computeFinalBounds(x, operations).1 <= n
{
    var low, high := x, x;
    assert 1 <= low <= high <= n;

    for i := 0 to |operations|
        invariant 0 <= i <= |operations|
        invariant 1 <= low <= high <= n
        invariant low == computeFinalBoundsHelper(x, x, operations, i).0
        invariant high == computeFinalBoundsHelper(x, x,
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
function computeFinalBoundsHelper(low: int, high: int, operations: seq<(int, int)>, index: int): (int, int)
    requires 0 <= index <= |operations|
    requires low <= high
    ensures computeFinalBoundsHelper(low, high, operations, index).0 <= computeFinalBoundsHelper(low, high, operations, index).1
{
    if index == |operations| then (low, high)
    else
        var (l, r) := operations[index];
        var newLow := if l < low then l else low;
        var newHigh := if r > high then r else high;
        computeFinalBoundsHelper(newLow, newHigh, operations, index + 1)
}

lemma FinalBoundsInBounds(n: int, x: int, operations: seq<(int, int)>)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        1 <= l <= r <= n
    requires 1 <= x <= n
    ensures 1 <= computeFinalBounds(x, operations).0 <= computeFinalBounds(x, operations).1 <= n
{
    var low, high := x, x;
    assert 1 <= low <= high <= n;

    for i := 0 to |operations|
        invariant 0 <= i <= |operations|
        invariant 1 <= low <= high <= n
        invariant low == computeFinalBoundsHelper(x, x, operations, i).0
        invariant high == computeFinalBoundsHelper(x, x,
// </vc-code>

