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
    requires 0 <= index <= |operations|
    requires minBound <= maxBound
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    decreases |operations| - index
{
    if index == |operations| then
        (minBound, maxBound)
    else
        var (l, r) := operations[index];
        if l <= minBound && maxBound <= r then
            computeFinalBoundsHelper(minBound, maxBound, operations, index + 1)
        else
            var newMin := if l < minBound then l else minBound;
            var newMax := if r > maxBound then r else maxBound;
            computeFinalBoundsHelper(newMin, newMax, operations, index + 1)
}

lemma computeFinalBoundsHelperProperties(x: int, operations: seq<(int, int)>)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    ensures var (minB, maxB) := computeFinalBounds(x, operations);
            minB <= x <= maxB
{
    var result := computeFinalBounds(x, operations);
    assert result == computeFinalBoundsHelper(x, x, operations, 0);
    computeFinalBoundsHelperInvariant(x, x, operations, 0);
}

lemma computeFinalBoundsHelperInvariant(minBound: int, maxBound: int, operations: seq<(int, int)>, index: int)
    requires 0 <= index <= |operations|
    requires minBound <= maxBound
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    ensures var (resMin, resMax) := computeFinalBoundsHelper(minBound, maxBound, operations, index);
            resMin <= minBound && maxBound <= resMax
    decreases |operations| - index
{
    if index == |operations| {
        // Base case: trivial
    } else {
        var (l, r) := operations[index];
        if l <= minBound && maxBound <= r {
            computeFinalBoundsHelperInvariant(minBound, maxBound, operations, index + 1);
        } else {
            var newMin := if l < minBound then l else minBound;
            var newMax := if r > maxBound then r else maxBound;
            computeFinalBoundsHelperInvariant(newMin, newMax, operations, index + 1);
        }
    }
}

lemma computeFinalBoundsHelperStep(minBound: int, maxBound: int, operations: seq<(int, int)>, index: int)
    requires 0 <= index < |operations|
    requires minBound <= maxBound
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
    ensures var (l, r) := operations[index];
            var newMin := if l <= minBound && maxBound <= r then minBound 
                          else if l < minBound then l else minBound;
            var newMax := if l <= minBound && maxBound <= r then maxBound 
                          else if r > maxBound then r else maxBound;
            computeFinalBoundsHelper(minBound, maxBound, operations, index) == 
            computeFinalBoundsHelper(newMin, newMax, operations, index + 1)
{
    // This lemma follows directly from the definition of computeFinalBoundsHelper
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
        
        var minBound := x;
        var maxBound := x;
        
        ghost var processed := computeFinalBoundsHelper(x, x, operations, 0);
        assert processed == computeFinalBounds(x, operations);
        
        for j := 0 to |operations|
            invariant 0 <= j <= |operations|
            invariant minBound <= x <= maxBound
            invariant 1 <= minBound <= maxBound <= n
            invariant (minBound, maxBound) == computeFinalBoundsHelper(x, x, operations[..j], 0)
            invariant computeFinalBoundsHelper(x, x, operations[..j], 0) == 
                     computeFinalBoundsHelper(computeFinalBoundsHelper(x, x, operations[..j], 0).0,
                                             computeFinalBoundsHelper(x, x, operations[..j], 0).1,
                                             operations[j..], 0)
        {
            var (l, r) := operations[j];
            
            ghost var oldMin := minBound;
            ghost var oldMax := maxBound;
            
            if l <= minBound && maxBound <= r {
                // Operation contains current bounds, no change needed
            } else {
                // Expand bounds if needed
                if l < minBound {
                    minBound := l;
                }
                if r > maxBound {
                    maxBound := r;
                }
            }
            
            assert operations[..j+1] == operations[..j] + [operations[j]];
            computeFinalBoundsHelperStep(oldMin, oldMax, [operations[j]], 0);
        }
        
        assert operations[..|operations|] == operations;
        assert (minBound, maxBound) == computeFinalBounds(x, operations);
        computeFinalBoundsHelperProperties(x, operations);
        
        var rangeSize := maxBound - minBound + 1;
        results := results + [rangeSize];
    }
}
// </vc-code>

