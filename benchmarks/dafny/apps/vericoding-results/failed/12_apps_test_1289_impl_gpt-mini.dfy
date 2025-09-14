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
function countVisits(visits: seq<int>, v: int): int
  decreases |visits|
{
  if |visits| == 0 then 0 else (if visits[0] == v then 1 else 0) + countVisits(visits[1..], v)
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

function sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function maxVal(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else if s[0] >= maxVal(s[1..]) then s[0] else maxVal(s[1..])
}

lemma countVisits_contains_first(visits: seq<int>)
  requires |visits| >= 1
  ensures countVisits(visits, visits[0]) >= 1
  decreases visits
{
  // By the definition of countVisits, the first element contributes 1
  assert countVisits(visits, visits[0]) == 1 + countVisits(visits[1..], visits[0]);
  assert countVisits(visits, visits[0]) >= 1;
}

lemma computeCounts_has_positive(n: int, visits: seq<int>)
  requires n >= 2
  requires forall i :: 0 <= i < |visits| ==> 1 <= visits[i] <= n
  requires |visits| >= 1
{
  var idx := visits[0] - 1;
  assert 0 <= idx < n;
  // baseCounts[idx] == countVisits(visits, visits[0]) >= 1
  assert countVisits(visits, visits[0]) >= 1 by {
    countVisits_contains_first(visits);
  }
  var baseCounts := seq(n, i requires 0 <= i < n => countVisits(visits, i + 1));
  assert baseCounts[idx] >= 1;
  var counts := seq(n, i requires 0 <= i < n => if i == 0 || i == n - 1 then baseCounts[i] * 2 else baseCounts[i]);
  assert counts[idx] > 0;
}

lemma counts_allzero_implies_maxRounds_positive(counts: seq<int>, maxRounds: int)
  requires |counts| > 0
  requires forall i :: 0 <= i < |counts| ==> counts[i] - maxRounds * 2 == 0
  requires exists i :: 0 <= i < |counts| && counts[i] > 0
  ensures maxRounds >= 1
{
  var k :| 0 <= k < |counts| && counts[k] > 0;
  assert counts[k] == maxRounds * 2;
  assert maxRounds * 2 > 0;
  assert maxRounds >= 1;
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
    result := calculateTotalDistance(n, positions, visits);
  }
}
// </vc-code>

