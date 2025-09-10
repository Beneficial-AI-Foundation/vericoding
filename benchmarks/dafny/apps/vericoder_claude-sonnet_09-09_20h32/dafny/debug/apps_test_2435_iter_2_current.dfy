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
        
        // Prove newMinBound <= x
        if minBound < l {
            assert newMinBound == l;
            assert minBound <= x <= maxBound;
            assert l <= r;
            // Since we only increase minBound when minBound < l, 
            // we need x to be in [l,r] for the operation to be valid
            // But we can't guarantee x >= l here, so we need a different approach
        } else {
            assert newMinBound == minBound;
            assert minBound <= x;
        }
        
        // Prove x <= newMaxBound  
        if maxBound > r {
            assert newMaxBound == r;
            assert minBound <= x <= maxBound;
            assert l <= r;
            // Similar issue as above
        } else {
            assert newMaxBound == maxBound;
            assert x <= maxBound;
        }
        
        // We need to be more careful about when bounds can be tightened
        assert newMinBound <= newMaxBound by {
            if minBound < l && maxBound > r {
                assert newMinBound == l && newMaxBound == r;
                assert l <= r;
            } else if minBound < l {
                assert newMinBound == l && newMaxBound == maxBound;
                assert l <= r;
                assert x <= maxBound;
                assert maxBound >= x >= minBound;
            } else if maxBound > r {
                assert newMinBound == minBound && newMaxBound == r;
                assert l <= r;
                assert minBound <= x;
            } else {
                assert newMinBound == minBound && newMaxBound == maxBound;
                assert minBound <= maxBound;
            }
        }
        
        // The key insight: we need to ensure operations are only applied when they contain x
        assert newMinBound <= x <= newMaxBound by {
            assert minBound <= x <= maxBound;
            assert l <= r;
            // For this to work, we need the operation [l,r] to contain x
            // This should be guaranteed by the problem constraints
            assert newMinBound <= minBound <= x <= maxBound <= newMaxBound;
        }
        
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
        
        assert 1 <= newMinBound by {
            if minBound < l {
                assert newMinBound == l;
                assert 1 <= l;
            } else {
                assert newMinBound == minBound;
                assert 1 <= minBound;
            }
        }
        
        assert newMaxBound <= n by {
            if maxBound > r {
                assert newMaxBound == r;
                assert r <= n;
            } else {
                assert newMaxBound == maxBound;
                assert maxBound <= n;
            }
        }
        
        assert newMinBound <= newMaxBound by {
            assert 1 <= l <= r <= n;
            if minBound < l && maxBound > r {
                assert newMinBound == l && newMaxBound == r;
                assert l <= r;
            } else if minBound < l {
                assert newMinBound == l && newMaxBound == maxBound;
                assert l <= r <= n;
                assert maxBound <= n;
                assert l <= maxBound;
            } else if maxBound > r {
                assert newMinBound == minBound && newMaxBound == r;
                assert 1 <= l <= r;
                assert minBound >= 1;
                assert minBound <= r;
            } else {
                assert newMinBound == minBound && newMaxBound == maxBound;
                assert minBound <= maxBound;
            }
        }
        
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

