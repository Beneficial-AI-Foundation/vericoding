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
lemma SumSegmentCountsLemma(segments: seq<nat>)
    ensures SumSegmentCounts(segments) == if |segments| == 0 then 0 else SumSegmentCounts(segments[..|segments|-1]) + segments[|segments|-1] * (segments[|segments|-1] + 1) / 2
{
    if |segments| != 0 {
        calc {
            SumSegmentCounts(segments);
            ==
            segments[0] * (segments[0] + 1) / 2 + SumSegmentCounts(segments[1..]);
            == { SumSegmentCountsLemma(segments[1..]); }
            segments[0] * (segments[0] + 1) / 2 + SumSegmentCounts(segments[1..]);
            == { assert segments[1..] == segments[..|segments|-1][1..]; }
            SumSegmentCounts(segments[..|segments|-1]) + segments[|segments|-1] * (segments[|segments|-1] + 1) / 2;
        }
    }
}

lemma GetMaximalValidSegmentsLemma(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures |GetMaximalValidSegments(s, availableSet, startIdx)| <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx < |s| {
        var segmentLength := GetNextSegmentLength(s, availableSet, startIdx);
        if segmentLength == 0 {
            GetMaximalValidSegmentsLemma(s, availableSet, startIdx + 1);
        } else {
            var skipLength := SkipInvalidChars(s, availableSet, startIdx + segmentLength);
            var nextIdx := startIdx + segmentLength + skipLength;
            if nextIdx <= |s| {
                GetMaximalValidSegmentsLemma(s, availableSet, nextIdx);
            }
        }
    }
}

lemma GetNextSegmentLengthLemma(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures GetNextSegmentLength(s, availableSet, startIdx) <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx < |s| && s[startIdx] in availableSet {
        GetNextSegmentLengthLemma(s, availableSet, startIdx + 1);
    }
}

lemma CountValidSubstringsLemma(s: string, availableSet: set<char>)
    requires |s| > 0
    ensures CountValidSubstrings(s, availableSet) == CountValidSubstrings(s[..|s|-1], availableSet) + GetNextSegmentLength(s, availableSet, 0)
{
    if |s| == 1 {
        // Base case
        if s[0] in availableSet {
            assert CountValidSubstrings(s, availableSet) == 1;
            assert CountValidSubstrings(s[..0], availableSet) == 0;
            assert GetNextSegmentLength(s, availableSet, 0) == 1;
        } else {
            assert CountValidSubstrings(s, availableSet) == 0;
            assert CountValidSubstrings(s[..0], availableSet) == 0;
            assert GetNextSegmentLength(s, availableSet, 0) == 0;
        }
    } else if |s| > 1 {
        // Recursive case
        CountValidSubstringsLemma(s[..|s|-1], availableSet);
    }
}

lemma SegmentConsistencyLemma(s: string, availableSet: set<char>, i: nat)
    requires i < |s|
    ensures CountValidSubstrings(s[..i+1], availableSet) == CountValidSubstrings(s[..i], availableSet) + (if s[i] in availableSet then GetNextSegmentLength(s[..i+1], availableSet, 0) - GetNextSegmentLength(s[..i], availableSet, 0) else 0)
{
    CountValidSubstringsLemma(s[..i+1], availableSet);
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
    var availableSet := set c | c in available;
    var total := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant total == CountValidSubstrings(s[..i], availableSet)
        invariant total <= i * (i + 1) / 2
    {
        var count := 0;
        
        while i < n && s[i] in availableSet
            invariant 0 <= i <= n
            invariant total == CountValidSubstrings(s[..i], availableSet) + count * (count + 1) / 2
            invariant total <= i * (i + 1) / 2
            decreases n - i
        {
            count := count + 1;
            total := total + count;
            i := i + 1;
        }
        
        if i < n && s[i] !in availableSet {
            i := i + 1;
        }
    }
    
    result := total;
}
// </vc-code>

