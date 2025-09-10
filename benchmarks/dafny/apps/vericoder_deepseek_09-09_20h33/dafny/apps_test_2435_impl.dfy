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
function computeFinalBoundsHelper(l: int, r: int, operations: seq<(int, int)>, index: int): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (opL, opR) := operations[j];
        opL <= opR
    requires 0 <= index <= |operations|
    requires 1 <= l <= r
    decreases |operations| - index
{
    if index >= |operations| then
        (l, r)
    else
        var (opL, opR) := operations[index];
        var newL := if opL <= l && l <= opR then opL else l;
        var newR := if opL <= r && r <= opR then opR else r;
        assert 1 <= newL <= newR;
        computeFinalBoundsHelper(newL, newR, operations, index + 1)
}

lemma ValidResultsEmpty()
    ensures ValidResults([], [])
{
}

lemma ValidResultsExtend(testCases: seq<(int, int, seq<(int, int)>)>, results: seq<int>, n: int, x: int, operations: seq<(int, int)>, finalL: int, finalR: int)
    requires ValidInput(testCases)
    requires ValidResults(testCases, results)
    requires |testCases| >= 0
    requires n >= 1 && 1 <= x <= n
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        1 <= l <= r <= n
    requires 1 <= finalL <= finalR <= n
    requires finalL <= x <= finalR
    ensures ValidResults(testCases + [(n, x, operations)], results + [finalR - finalL + 1])
{
}

lemma ComputeFinalBoundsPreservesBounds(x: int, operations: seq<(int, int)>)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    requires 1 <= x
    ensures var (l, r) := computeFinalBounds(x, operations);
        1 <= l <= r
{
    var (l, r) := computeFinalBounds(x, operations);
    assert 1 <= l <= r;
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
    var i := 0;
    ValidResultsEmpty();
    while i < |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant ValidResults(testCases[0..i], results)
    {
        var (n, x, operations) := testCases[i];
        var (finalL, finalR) := computeFinalBounds(x, operations);
        ComputeFinalBoundsPreservesBounds(x, operations);
        assert 1 <= finalL <= finalR <= n;
        assert finalL <= x <= finalR;
        ValidResultsExtend(testCases[0..i], results, n, x, operations, finalL, finalR);
        results := results + [finalR - finalL + 1];
        i := i + 1;
    }
}
// </vc-code>

