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
function computeFinalBoundsHelper(currentL: int, currentR: int, operations: seq<(int, int)>, k: int): (int, int)
    requires currentL <= currentR
    requires 0 <= k <= |operations|
    decreases |operations| - k
    ensures var (finalL, finalR) := result; finalL <= finalR
    ensures var (finalL, finalR) := result; finalL <= currentL
    ensures var (finalL, finalR) := result; finalR >= currentR
{
    if k == |operations| then
        (currentL, currentR)
    else
        var (l_k, r_k) := operations[k];
        var nextL, nextR: int;

        if r_k < currentL || l_k > currentR then
            // No overlap, bounds remain unchanged
            nextL := currentL;
            nextR := currentR;
        else
            // Overlap, update bounds
            nextL := max(currentL, l_k);
            nextR := min(currentR, r_k);
        
        computeFinalBoundsHelper(max(1, nextL), nextR, operations, k + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
    results := new int[|testCases|];
    for i := 0 to |testCases| - 1
        invariant 0 <= i < |testCases| + 1
        invariant |results| == |testCases|
        invariant forall j :: 0 <= j < i ==> 
            var (n_j, x_j, operations_j) := testCases[j];
            var (finalL_j, finalR_j) := computeFinalBounds(x_j, operations_j);
            results[j] == finalR_j - finalL_j + 1 &&
            finalL_j <= x_j <= finalR_j &&
            results[j] >= 1 &&
            1 <= finalL_j <= finalR_j <= n_j
    {
        var (n, x, operations) := testCases[i];
        var (finalL, finalR) := computeFinalBounds(x, operations);
        
        // Assertions based on ValidInput and postconditions of computeFinalBounds
        assert finalL <= finalR;
        assert finalL <= x <= finalR; // computeFinalBoundsHelper ensures this by construction
        assert 1 <= finalL; // From the max(1, nextL) in computeFinalBoundsHelper
        assert finalR <= n; // Constraint from the problem statement: operations are within [1, n], 
                            // and the initial bounds are within [1, n] (x is 1 <= x <= n).
                            // computeFinalBoundsHelper continuously shrinks towards the common interval
                            // or keeps the original interval if no overlap, so it will not exceed n.

        results[i] := finalR - finalL + 1;
    }
    return results;
}
// </vc-code>

