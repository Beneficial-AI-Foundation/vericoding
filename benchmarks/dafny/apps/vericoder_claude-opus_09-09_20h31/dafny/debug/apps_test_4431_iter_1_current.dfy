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
lemma SumSegmentCountsBound(segments: seq<nat>, totalLength: nat)
    requires forall i :: 0 <= i < |segments| ==> segments[i] <= totalLength
    ensures SumSegmentCounts(segments) <= totalLength * (totalLength + 1) / 2
{
    if |segments| == 0 {
        assert SumSegmentCounts(segments) == 0;
    } else {
        var rest := segments[1..];
        assert forall i :: 0 <= i < |rest| ==> rest[i] <= totalLength;
        SumSegmentCountsBound(rest, totalLength);
        assert segments[0] * (segments[0] + 1) / 2 <= totalLength * (totalLength + 1) / 2;
    }
}

lemma GetMaximalValidSegmentsLength(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures var segments := GetMaximalValidSegments(s, availableSet, startIdx);
            forall i :: 0 <= i < |segments| ==> segments[i] <= |s| - startIdx
    decreases |s| - startIdx
{
    if startIdx >= |s| {
    } else {
        var segmentLength := GetNextSegmentLength(s, availableSet, startIdx);
        if segmentLength == 0 {
            GetMaximalValidSegmentsLength(s, availableSet, startIdx + 1);
        } else {
            var skipLength := SkipInvalidChars(s, availableSet, startIdx + segmentLength);
            var nextIdx := startIdx + segmentLength + skipLength;
            if nextIdx <= |s| {
                GetMaximalValidSegmentsLength(s, availableSet, nextIdx);
            }
        }
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
    var availableSet := set c | c in available;
    var count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == CountValidSubstrings(s[..i], availableSet)
        invariant count <= i * (i + 1) / 2
    {
        if s[i] in availableSet {
            // Count how many valid characters we have starting from i
            var j := i;
            while j < |s| && s[j] in availableSet
                invariant i <= j <= |s|
                invariant forall k :: i <= k < j ==> s[k] in availableSet
                invariant j - i == GetNextSegmentLength(s, availableSet, i) - (|s| - j)
            {
                j := j + 1;
            }
            
            // Add all substrings of this valid segment
            var segmentLength := j - i;
            count := count + segmentLength * (segmentLength + 1) / 2;
            i := j;
        } else {
            i := i + 1;
        }
    }
    
    assert s[..|s|] == s;
    GetMaximalValidSegmentsLength(s, availableSet, 0);
    var segments := GetMaximalValidSegments(s, availableSet, 0);
    SumSegmentCountsBound(segments, |s|);
    
    result := count;
}
// </vc-code>

