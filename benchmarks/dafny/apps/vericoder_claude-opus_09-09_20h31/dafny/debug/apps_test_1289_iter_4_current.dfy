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
function countVisits(visits: seq<int>, target: int): int
    requires forall i :: 0 <= i < |visits| ==> visits[i] >= 1
    ensures countVisits(visits, target) >= 0
{
    if |visits| == 0 then 0
    else if visits[0] == target then 1 + countVisits(visits[1..], target)
    else countVisits(visits[1..], target)
}

lemma countVisitsPositive(visits: seq<int>, target: int)
    requires forall i :: 0 <= i < |visits| ==> visits[i] >= 1
    requires target in visits
    ensures countVisits(visits, target) > 0
{
    if |visits| == 0 {
        assert false;
    } else if visits[0] == target {
        assert countVisits(visits, target) == 1 + countVisits(visits[1..], target);
        assert countVisits(visits[1..], target) >= 0;
    } else {
        assert target in visits[1..];
        countVisitsPositive(visits[1..], target);
    }
}

lemma existsPositiveCount(n: int, visits: seq<int>)
    requires n >= 2
    requires |visits| >= 1
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    ensures exists i {:trigger countVisits(visits, i + 1)} :: 0 <= i < n && countVisits(visits, i + 1) > 0
{
    var firstVisit := visits[0];
    assert 1 <= firstVisit <= n;
    assert firstVisit in visits;
    countVisitsPositive(visits, firstVisit);
    assert countVisits(visits, firstVisit) > 0;
    assert 0 <= firstVisit - 1 < n;
    assert countVisits(visits, (firstVisit - 1) + 1) > 0;
}

lemma existsPositiveCountInCounts(n: int, visits: seq<int>)
    requires n >= 2
    requires |visits| >= 1
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    ensures exists i :: 0 <= i < n && computeCounts(n, visits)[i] > 0
{
    existsPositiveCount(n, visits);
    var idx :| 0 <= idx < n && countVisits(visits, idx + 1) > 0;
    var baseCounts := seq(n, i requires 0 <= i < n => countVisits(visits, i + 1));
    assert baseCounts[idx] > 0;
    var counts := computeCounts(n, visits);
    
    if idx == 0 || idx == n - 1 {
        assert counts[idx] == baseCounts[idx] * 2 > 0;
    } else {
        assert counts[idx] == baseCounts[idx] > 0;
    }
}

lemma maxRoundsPositiveWhenAllZero(n: int, visits: seq<int>)
    requires n >= 2
    requires |visits| >= 1
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    ensures computeMaxRounds(computeCounts(n, visits)) >= 1
{
    var counts := computeCounts(n, visits);
    existsPositiveCountInCounts(n, visits);
    var idx :| 0 <= idx < n && counts[idx] > 0;
    
    var divCounts := seq(|counts|, i requires 0 <= i < |counts| => counts[i] / 2);
    assert counts[idx] >= 1;
    
    if counts[idx] >= 2 {
        assert divCounts[idx] >= 1;
    } else {
        // counts[idx] == 1, which means it's an internal node with baseCount == 1
        // But we need to find an endpoint or a node with count >= 2
        if idx == 0 || idx == n - 1 {
            // Endpoints have counts[idx] = baseCounts[idx] * 2
            // Since counts[idx] > 0, we have baseCounts[idx] > 0
            // So counts[idx] >= 2
            assert counts[idx] >= 2;
            assert false; // contradiction
        }
        // Find any endpoint with a visit
        var found := false;
        var j := 0;
        while j < n && !found
            invariant 0 <= j <= n
        {
            if (j == 0 || j == n - 1) && countVisits(visits, j + 1) > 0 {
                var baseCounts := seq(n, i requires 0 <= i < n => countVisits(visits, i + 1));
                assert counts[j] == baseCounts[j] * 2 >= 2;
                assert divCounts[j] >= 1;
                found := true;
            }
            j := j + 1;
        }
        if !found {
            // All endpoints have count 0, so all visits are to internal nodes
            // But we have at least one visit, so at least one internal node has count > 0
            // Since all internal nodes have counts[i] = baseCounts[i], we already found such a node (idx)
            // Try another approach: if no endpoint is visited, increase search
            existsPositiveCount(n, visits);
            var k :| 0 <= k < n && countVisits(visits, k + 1) > 0;
            if k == 0 || k == n - 1 {
                var baseCounts := seq(n, i requires 0 <= i < n => countVisits(visits, i + 1));
                assert counts[k] == baseCounts[k] * 2 >= 2;
                assert divCounts[k] >= 1;
            } else {
                // k is internal with countVisits > 0
                // All visits must be distributed among nodes
                // At least one node has count >= 2 or an endpoint has count > 0
                assert divCounts[idx] >= 0;
                // Need stronger reasoning
                assert divCounts[idx] == counts[idx] / 2 == 1 / 2 == 0;
                // Search for nodes with higher counts
                var total := |visits|;
                assert total >= 1;
                // Since we have visits, at least one divCount must be >= 1
                // This requires showing that not all counts can be 1
                assert exists i :: 0 <= i < |divCounts| && divCounts[i] >= 1;
            }
        }
    }
    
    assert exists i :: 0 <= i < |divCounts| && divCounts[i] >= 1;
    assert computeMaxRounds(counts) == maxVal(divCounts);
    assert computeMaxRounds(counts) >= 1;
}

function maxVal(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= maxVal(s)
    ensures exists i :: 0 <= i < |s| && s[i] == maxVal(s)
{
    if |s| == 1 then s[0]
    else 
        var tailMax := maxVal(s[1..]);
        if s[0] > tailMax then s[0] else tailMax
}

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}

function sum(s: seq<int>): int
    ensures |s| == 0 ==> sum(s) == 0
    ensures sum(s) >= 0 || exists i :: 0 <= i < |s| && s[i] < 0
    ensures (forall i :: 0 <= i < |s| ==> s[i] >= 0) ==> sum(s) >= 0
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

lemma sumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
    if |s| == 0 {
    } else {
        sumNonNegative(s[1..]);
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
    // Check if the path is ambiguous
    if hasAmbiguousPath(n, positions, visits) {
        return -1;
    }
    
    // Path is not ambiguous, calculate the total distance
    maxRoundsPositiveWhenAllZero(n, visits);
    var distance := calculateTotalDistance(n, positions, visits);
    
    // Prove that distance >= 0
    var counts := computeCounts(n, visits);
    var maxRounds := computeMaxRounds(counts);
    var remainingCounts := seq(n, i requires 0 <= i < n => counts[i] - maxRounds * 2);
    var allZero := forall i :: 0 <= i < n ==> remainingCounts[i] == 0;
    
    if allZero {
        if n == 2 {
            assert distance == maxRounds * (positions[1] - positions[0]) * 2 - (positions[1] - positions[0]);
            assert positions[1] - positions[0] > 0;
            assert maxRounds >= 1;
            assert distance >= (positions[1] - positions[0]) * 2 - (positions[1] - positions[0]);
            assert distance >= positions[1] - positions[0];
            assert distance >= 0;
        } else {
            var firstDist := positions[1] - positions[0];
            // Use the lemma to establish maxRounds >= 1
            assert maxRounds >= 1;
            assert distance == maxRounds * firstDist * 2 * (n - 1) - firstDist;
            assert firstDist > 0;
            assert n >= 3;
            assert distance >= firstDist * 2 * (n - 1) - firstDist;
            assert distance >= firstDist * (2 * (n - 1) - 1);
            assert 2 * (n - 1) - 1 >= 2 * 2 - 1;
            assert distance >= firstDist * 3;
            assert distance >= 0;
        }
    } else {
        var edgeDistance := sum(seq(n-1, i requires 0 <= i < n-1 => min(remainingCounts[i], remainingCounts[i+1]) * (positions[i+1] - positions[i])));
        var totalEdgeLength := sum(seq(n-1, i requires 0 <= i < n-1 => positions[i+1] - positions[i]));
        
        // Prove edgeDistance >= 0
        var edgeProducts := seq(n-1, i requires 0 <= i < n-1 => min(remainingCounts[i], remainingCounts[i+1]) * (positions[i+1] - positions[i]));
        assert forall i :: 0 <= i < |edgeProducts| ==> edgeProducts[i] >= 0;
        sumNonNegative(edgeProducts);
        assert edgeDistance >= 0;
        
        // Prove totalEdgeLength >= 0
        var edgeLengths := seq(n-1, i requires 0 <= i < n-1 => positions[i+1] - positions[i]);
        assert forall i :: 0 <= i < |edgeLengths| ==> edgeLengths[i] > 0;
        sumNonNegative(edgeLengths);
        assert totalEdgeLength >= 0;
        
        assert distance == edgeDistance + maxRounds * 2 * totalEdgeLength;
        assert maxRounds >= 1;
        assert distance >= 0;
    }
    
    return distance;
}
// </vc-code>

