predicate ValidInput(n: nat, k: nat, s: string, available: seq<char>)
{
    n == |s| &&
    k == |available| &&
    forall i, j :: 0 <= i < j < |available| ==> available[i] != available[j]
}

function CountValidSubstrings(s: string, availableSet: set<char>): nat
{
    if |s| == 0 then 0
    else
        var segments := GetMaximalValidSegments(s, availableSet, 0);
        SumSegmentCounts(segments)
}

function GetMaximalValidSegments(s: string, availableSet: set<char>, startIdx: nat): seq<nat>
    requires startIdx <= |s|
    decreases |s| - startIdx
{
    if startIdx >= |s| then []
    else
        var segmentLength := GetNextSegmentLength(s, availableSet, startIdx);
        if segmentLength == 0 then
            GetMaximalValidSegments(s, availableSet, startIdx + 1)
        else
            var skipLength := SkipInvalidChars(s, availableSet, startIdx + segmentLength);
            var nextIdx := startIdx + segmentLength + skipLength;
            if nextIdx <= |s| then
                [segmentLength] + GetMaximalValidSegments(s, availableSet, nextIdx)
            else
                [segmentLength]
}

function GetNextSegmentLength(s: string, availableSet: set<char>, startIdx: nat): nat
    requires startIdx <= |s|
    ensures GetNextSegmentLength(s, availableSet, startIdx) <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx >= |s| || s[startIdx] !in availableSet then 0
    else 1 + GetNextSegmentLength(s, availableSet, startIdx + 1)
}

function SkipInvalidChars(s: string, availableSet: set<char>, startIdx: nat): nat
    requires startIdx <= |s|
    ensures SkipInvalidChars(s, availableSet, startIdx) <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx >= |s| || s[startIdx] in availableSet then 0
    else 1 + SkipInvalidChars(s, availableSet, startIdx + 1)
}

function SumSegmentCounts(segments: seq<nat>): nat
{
    if |segments| == 0 then 0
    else segments[0] * (segments[0] + 1) / 2 + SumSegmentCounts(segments[1..])
}

// <vc-helpers>
function SeqSum(xs: seq<nat>): nat
{
    if |xs| == 0 then 0 else xs[0] + SeqSum(xs[1..])
}

lemma SumSegmentCounts_le_sumSum(xs: seq<nat>)
    ensures SumSegmentCounts(xs) <= SeqSum(xs) * (SeqSum(xs) + 1) / 2
    decreases |xs|
{
    if |xs| == 0 {
        // SumSegmentCounts([]) == 0 and SeqSum([]) == 0
    } else {
        var x := xs[0];
        var rest := xs[1..];
        SumSegmentCounts_le_sumSum(rest);
        var restSum := SeqSum(rest);
        assert SeqSum(xs) == x + restSum;
        assert 2 * SumSegmentCounts(rest) <= restSum * (restSum + 1);
        assert x * (x + 1) + 2 * SumSegmentCounts(rest) <= x * (x + 1) + restSum * (restSum + 1);
        assert x * (x + 1) + restSum * (restSum + 1) + 2 * x * restSum == (x + restSum) * (x + restSum + 1);
        assert 2 * (x * (x + 1) / 2 + SumSegmentCounts(rest)) <= (x + restSum) * (x + restSum + 1);
        assert x * (x + 1) / 2 + SumSegmentCounts(rest) <= (x + restSum) * (x + restSum + 1) / 2;
    }
}

lemma GetMaximalSegments_sum_le(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures SeqSum(GetMaximalValidSegments(s, availableSet, startIdx)) <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx >= |s| {
        // trivial: GetMaximalValidSegments returns []
    } else {
        var segLen := GetNextSegmentLength(s, availableSet, startIdx);
        if segLen == 0 {
            GetMaximalSegments_sum_le(s, availableSet, startIdx + 1);
            assert SeqSum(GetMaximalValidSegments(s, availableSet, startIdx)) == SeqSum(GetMaximalValidSegments(s, availableSet, startIdx + 1));
        } else {
            var skip := SkipInvalidChars(s, availableSet, startIdx + segLen);
            var nextIdx := startIdx + segLen + skip;
            GetMaximalSegments_sum_le(s, availableSet, nextIdx);
            var restSum := SeqSum(GetMaximalValidSegments(s, availableSet, nextIdx));
            assert SeqSum(GetMaximalValidSegments(s, availableSet, startIdx)) == segLen + restSum;
            assert restSum <= |s| - nextIdx;
            assert segLen + restSum <= segLen + (|s| - nextIdx);
            assert segLen + (|s| - nextIdx) == segLen + (|s| - (startIdx + segLen + skip));
            assert segLen + (|s| - (startIdx + segLen + skip)) == |s| - startIdx - skip;
            assert |s| - startIdx - skip <= |s| - startIdx;
        }
    }
}

lemma TriangularMonotone(a: nat, b: nat)
    requires a <= b
    ensures a * (a + 1) / 2 <= b * (b + 1) / 2
{
    assert b * (b + 1) - a * (a + 1) == (b - a) * (b + a + 1);
    assert (b - a) * (b + a + 1) >= 0;
}

lemma CountValidSubstrings_Bounded(s: string, availableSet: set<char>)
    ensures CountValidSubstrings(s, availableSet) <= |s| * (|s| + 1) / 2
{
    if |s| == 0 {
        // CountValidSubstrings == 0
    } else {
        var segments := GetMaximalValidSegments(s, availableSet, 0);
        GetMaximalSegments_sum_le(s, availableSet, 0);
        SumSegmentCounts_le_sumSum(segments);
        var ss := SeqSum(segments);
        assert ss <= |s|;
        TriangularMonotone(ss, |s|);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, k: nat, s: string, available: seq<char>) returns (result: nat)
    requires ValidInput(n, k, s, available)
    ensures result <= n * (n + 1) / 2
    ensures result == CountValidSubstrings(s, set c | c in available)
// </vc-spec>
// <vc-code>
{
  result := CountValidSubstrings(s, set c | c in available);
  CountValidSubstrings_Bounded(s, set c | c in available);
}
// </vc-code>

