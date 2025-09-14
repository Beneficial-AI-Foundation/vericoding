predicate isSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate allDistancesEqual(positions: seq<int>)
    requires |positions| >= 2
    requires forall i :: 0 <= i < |positions| - 1 ==> positions[i] < positions[i + 1]
{
    if |positions| <= 2 then true
    else
        var firstDist := positions[1] - positions[0];
        forall i :: 1 <= i < |positions| - 1 ==> positions[i + 1] - positions[i] == firstDist
}

function computeCounts(n: int, visits: seq<int>): seq<int>
    requires n >= 2
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
{
    var baseCounts := seq(n, i requires 0 <= i < n => countVisits(visits, i + 1));
    seq(n, i requires 0 <= i < n => 
        if i == 0 || i == n - 1 then baseCounts[i] * 2 
        else baseCounts[i]
    )
}

function computeMaxRounds(counts: seq<int>): int
    requires |counts| > 0
{
    maxVal(seq(|counts|, i requires 0 <= i < |counts| => counts[i] / 2))
}

predicate hasAmbiguousPath(n: int, positions: seq<int>, visits: seq<int>)
    requires n >= 2
    requires |positions| == n
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    requires forall i :: 0 <= i < n - 1 ==> positions[i] < positions[i + 1]
{
    var counts := computeCounts(n, visits);
    var maxRounds := computeMaxRounds(counts);
    var remainingCounts := seq(n, i requires 0 <= i < n => counts[i] - maxRounds * 2);
    var allZero := forall i :: 0 <= i < n ==> remainingCounts[i] == 0;

    allZero && n > 2 && !allDistancesEqual(positions)
}

function calculateTotalDistance(n: int, positions: seq<int>, visits: seq<int>): int
    requires n >= 2
    requires |positions| == n
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    requires forall i :: 0 <= i < n - 1 ==> positions[i] < positions[i + 1]
    requires !hasAmbiguousPath(n, positions, visits)
    requires |visits| >= 1
    ensures calculateTotalDistance(n, positions, visits) >= 0
{
    var counts := computeCounts(n, visits);
    var maxRounds := computeMaxRounds(counts);
    var remainingCounts := seq(n, i requires 0 <= i < n => counts[i] - maxRounds * 2);
    var allZero := forall i :: 0 <= i < n ==> remainingCounts[i] == 0;

    if allZero then
        if n == 2 then
            maxRounds * (positions[1] - positions[0]) * 2 - (positions[1] - positions[0])
        else
            var firstDist := positions[1] - positions[0];
            // Since |visits| >= 1, there must be at least one visit
            // This means at least one count > 0, so if allZero then maxRounds >= 1
            assert exists i :: 0 <= i < n && counts[i] > 0;
            assert maxRounds >= 1;
            maxRounds * firstDist * 2 * (n - 1) - firstDist
    else
        var edgeDistance := sum(seq(n-1, i requires 0 <= i < n-1 => min(remainingCounts[i], remainingCounts[i+1]) * (positions[i+1] - positions[i])));
        var totalEdgeLength := sum(seq(n-1, i requires 0 <= i < n-1 => positions[i+1] - positions[i]));
        edgeDistance + maxRounds * 2 * totalEdgeLength
}

// <vc-helpers>
function countVisits(visits: seq<int>, node: int): nat
    requires 1 <= node
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i]
{
    if |visits| == 0 then 0
    else (if visits[0] == node then 1 else 0) + countVisits(visits[1..], node)
}

function maxVal(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= maxVal(s)
    ensures exists i :: 0 <= i < |s| && s[i] == maxVal(s)
{
    if |s| == 1 then s[0]
    else
        var maxRest := maxVal(s[1..]);
        if s[0] > maxRest then s[0] else maxRest
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma CountVisitsLemma(visits: seq<int>, node: int)
    requires 1 <= node
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i]
    ensures countVisits(visits, node) >= 0
{
}

lemma MaxValLemma(s: seq<int>)
    requires |s| > 0
    ensures maxVal(s) >= 0 || exists i :: 0 <= i < |s| && s[i] < 0
{
}

lemma SumLemma(s: seq<int>)
    ensures sum(s) >= 0 || exists i :: 0 <= i < |s| && s[i] < 0
{
}

lemma ComputeMaxRoundsNonNegative(counts: seq<int>)
    requires |counts| > 0
    requires forall i :: 0 <= i < |counts| ==> counts[i] >= 0
    ensures computeMaxRounds(counts) >= 0
{
    if |counts| == 1 {
        assert computeMaxRounds(counts) == counts[0] / 2;
        assert counts[0] / 2 >= 0;
    } else {
        var maxRest := computeMaxRounds(counts[1..]);
        ComputeMaxRoundsNonNegative(counts[1..]);
        if counts[0] / 2 > maxRest {
            assert computeMaxRounds(counts) == counts[0] / 2;
            assert counts[0] / 2 >= 0;
        } else {
            assert computeMaxRounds(counts) == maxRest;
            assert maxRest >= 0;
        }
    }
}

lemma RemainingCountsNonNegative(counts: seq<int>, maxRounds: int)
    requires |counts| > 0
    requires maxRounds >= 0
    requires forall i :: 0 <= i < |counts| ==> counts[i] >= 0
    ensures forall i :: 0 <= i < |counts| ==> counts[i] - maxRounds * 2 >= -1
{
    forall i | 0 <= i < |counts|
        ensures counts[i] - maxRounds * 2 >= -1
    {
        var r := counts[i] / 2;
        assert maxRounds >= r;
        assert counts[i] - maxRounds * 2 <= counts[i] - r * 2;
        assert counts[i] - r * 2 == counts[i] % 2;
        assert 0 <= counts[i] % 2 <= 1;
        assert counts[i] - maxRounds * 2 >= -1;
    }
}

lemma ExistsPositiveCount(counts: seq<int>)
    requires |counts| > 0
    requires sum(counts) > 0
    ensures exists i :: 0 <= i < |counts| && counts[i] > 0
{
    if |counts| == 1 {
        assert sum(counts) == counts[0];
        assert counts[0] > 0;
    } else {
        if counts[0] > 0 {
            // Found positive element
        } else {
            // Recursively check the rest
            var restSum := sum(counts[1..]);
            assert restSum > 0;
            ExistsPositiveCount(counts[1..]);
        }
    }
}

lemma MaxRoundsMin(counts: seq<int>)
    requires |counts| > 0
    requires forall i :: 0 <= i < |counts| ==> counts[i] >= 0
    ensures forall i :: 0 <= i < |counts| ==> computeMaxRounds(counts) >= 0
{
    ComputeMaxRoundsNonNegative(counts);
}

lemma AllZeroImpliesMaxRoundsCalculator(counts: seq<int>)
    requires |counts| > 0
    requires forall i :: 0 <= i < |counts| ==> counts[i] >= 0
    requires forall i :: 0 <= i < |counts| ==> counts[i] - computeMaxRounds(counts) * 2 == 0
    ensures sum(counts) > 0 ==> computeMaxRounds(counts) >= 1 || exists i :: 0 <= i < |counts| && counts[i] == 1
{
    if sum(counts) > 0 {
        ExistsPositiveCount(counts);
        var i :| 0 <= i < |counts| && counts[i] > 0;
        var r := computeMaxRounds(counts);
        assert counts[i] - r * 2 == 0;
        assert counts[i] == 2 * r;
        if counts[i] == 1 {
            assert r == 0;
        } else {
            assert r >= 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, positions: seq<int>, m: int, visits: seq<int>) returns (result: int)
    requires n >= 2
    requires |positions| == n
    requires m >= 1
    requires |visits| == m
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    requires forall i :: 0 <= i < n - 1 ==> positions[i] < positions[i + 1]
    requires forall i :: 0 <= i < |positions| ==> positions[i] >= 1
    requires isSorted(visits)
    ensures result >= -1
    ensures result == -1 <==> hasAmbiguousPath(n, positions, visits)
    ensures result >= 0 ==> result == calculateTotalDistance(n, positions, visits)
    ensures result >= 0 ==> (forall i :: 0 <= i < n-1 ==> positions[i+1] - positions[i] > 0)
// </vc-spec>
// <vc-code>
{
    if hasAmbiguousPath(n, positions, visits) {
        result := -1;
    } else {
        var counts := computeCounts(n, visits);
        ComputeMaxRoundsNonNegative(counts);
        var maxRounds := computeMaxRounds(counts);
        
        // Ensure maxRounds is non-negative
        assert maxRounds >= 0;
        
        var remainingCounts := seq(n, i requires 0 <= i < n => counts[i] - maxRounds * 2);
        RemainingCountsNonNegative(counts, maxRounds);
        
        var allZero := forall i :: 0 <= i < n ==> remainingCounts[i] == 0;
        
        // Show that there must be at least one positive count since |visits| >= 1
        var totalCount := sum(counts);
        ExistsPositiveCount(counts);
        assert totalCount > 0;
        assert exists i :: 0 <= i < n && counts[i] > 0;

        if allZero {
            // Verify that maxRounds is at least 1 when there's at least one positive count
            AllZeroImpliesMaxRoundsCalculator(counts);
            var i :| 0 <= i < n && counts[i] > 0;
            if counts[i] == 1 {
                assert maxRounds == 0;
            } else {
                assert maxRounds >= 1;
            }
            
            if n == 2 {
                result := maxRounds * (positions[1] - positions[0]) * 2 - (positions[1] - positions[0]);
            } else {
                var firstDist := positions[1] - positions[0];
                result := maxRounds * firstDist * 2 * (n - 1) - firstDist;
            }
        } else {
            var totalEdgeLength := 0;
            var i := 0;
            while i < n - 1
                invariant 0 <= i <= n - 1
                invariant totalEdgeLength >= 0
                invariant totalEdgeLength == sum(seq(i, j requires 0 <= j < i => positions[j + 1] - positions[j]))
            {
                totalEdgeLength := totalEdgeLength + (positions[i + 1] - positions[i]);
                i := i + 1;
            }
            
            var edgeDistance := 0;
            i := 0;
            while i < n - 1
                invariant 0 <= i <= n - 1
                invariant edgeDistance >= 0
                invariant edgeDistance == sum(seq(i, j requires 0 <= j < i => 
                    if remainingCounts[j] >= 0 && remainingCounts[j + 1] >= 0 
                    then min(remainingCounts[j], remainingCounts[j + 1]) * (positions[j + 1] - positions[j]) 
                    else 0))
            {
                if remainingCounts[i] >= 0 && remainingCounts[i + 1] >= 0 {
                    var minCount := min(remainingCounts[i], remainingCounts[i + 1]);
                    edgeDistance := edgeDistance + minCount * (positions[i + 1] - positions[i]);
                }
                i := i + 1;
            }
            
            result := edgeDistance + maxRounds * 2 * totalEdgeLength;
        }
    }
}
// </vc-code>

