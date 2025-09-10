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
function computeFinalBoundsHelper(currL: int, currR: int, operations: seq<(int, int)>, k: int): (int, int)
    requires 0 <= k <= |operations|
    requires forall j :: 0 <= j < |operations| ==> operations[j].0 <= operations[j].1
    decreases |operations| - k
    ensures result.0 <= result.1
    ensures forall origX :: currL <= origX <= currR ==> result.0 <= origX <= result.1
    ensures forall n :: (forall j :: 0 <= j < |operations| ==> 1 <= operations[j].0 <= operations[j].1 <= n) && 1 <= currL <= currR <= n ==> 1 <= result.0 <= result.1 <= n
{
    if k >= |operations| then
        (currL, currR)
    else
        var op := operations[k];
        var a := op.0; var b := op.1;
        if b < currL || a > currR then
            computeFinalBoundsHelper(currL, currR, operations, k + 1)
        else
            var newL := if currL <= a then currL else a;
            var newR := if currR >= b then currR else b;
            computeFinalBoundsHelper(newL, newR, operations, k + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
    var res: seq<int> := [];
    var i := 0;
    while i < |testCases|
      invariant 0 <= i <= |testCases|
      invariant |res| == i
      invariant forall j :: 0 <= j < i ==> res[j] == computeFinalBounds(testCases[j].1, testCases[j].2).1 - computeFinalBounds(testCases[j].1, testCases[j].2).0 + 1
    {
        var tc := testCases[i];
        var x := tc.1;
        var ops := tc.2;
        var fb := computeFinalBounds(x, ops);
        var val := fb.1 - fb.0 + 1;
        res := res + [val];
        i := i + 1;
    }
    results := res;
}
// </vc-code>

