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
function countVisits(visits: seq<int>, position: int): int
{
    |set i | 0 <= i < |visits| && visits[i] == position|
}

function maxVal(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else
        var rest := maxVal(s[1..]);
        if s[0] > rest then s[0] else rest
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma CountVisitsNonNegative(visits: seq<int>, position: int)
    ensures countVisits(visits, position) >= 0
{
}

lemma MaxValBounds(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= maxVal(s)
{
    if |s| == 1 {
    } else {
        MaxValBounds(s[1..]);
    }
}

lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
}

lemma VisitsImplyNonZeroCounts(n: int, visits: seq<int>)
    requires n >= 2
    requires |visits| >= 1
    requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
    ensures exists i :: 0 <= i < n && countVisits(visits, i + 1) > 0
{
    assert 1 <= visits[0] <= n;
    assert countVisits(visits, visits[0]) > 0;
}

lemma MaxRoundsPositive(counts: seq<int>)
    requires |counts| > 0
    requires exists i :: 0 <= i < |counts| && counts[i] > 0
    ensures computeMaxRounds(counts) >= 1
{
    var i :| 0 <= i < |counts| && counts[i] > 0;
    var quotients := seq(|counts|, j requires 0 <= j < |counts| => counts[j] / 2);
    assert quotients[i] >= 0;
    if counts[i] >= 2 {
        assert quotients[i] >= 1;
        MaxValBounds(quotients);
        assert maxVal(quotients) >= quotients[i] >= 1;
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
    var counts := computeCounts(n, visits);
    var maxRounds := computeMaxRounds(counts);
    var remainingCounts := seq(n, i requires 0 <= i < n => counts[i] - maxRounds * 2);
    var allZero := forall i :: 0 <= i < n ==> remainingCounts[i] == 0;
    
    if allZero && n > 2 && !allDistancesEqual(positions) {
        result := -1;
    } else {
        result := calculateTotalDistance(n, positions, visits);
    }
}
// </vc-code>

