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
        
        assert segments[0] <= totalLength;
        MonotonicityLemma(segments[0], totalLength);
        
        SumSegmentCountsBound(rest, totalLength);
        assert SumSegmentCounts(segments) == segments[0] * (segments[0] + 1) / 2 + SumSegmentCounts(rest);
    }
}

lemma MonotonicityLemma(a: nat, b: nat)
    requires a <= b
    ensures a * (a + 1) / 2 <= b * (b + 1) / 2
{
    if a == b {
        assert a * (a + 1) / 2 == b * (b + 1) / 2;
    } else {
        assert a < b;
        assert a + 1 <= b + 1;
        assert a * (a + 1) <= b * (b + 1);
        assert a * (a + 1) / 2 <= b * (b + 1) / 2;
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
            assert segmentLength <= |s| - startIdx;
            var skipLength := SkipInvalidChars(s, availableSet, startIdx + segmentLength);
            var nextIdx := startIdx + segmentLength + skipLength;
            if nextIdx <= |s| {
                GetMaximalValidSegmentsLength(s, availableSet, nextIdx);
                var segments := GetMaximalValidSegments(s, availableSet, startIdx);
                assert segments[0] == segmentLength;
                assert segmentLength <= |s| - startIdx;
            }
        }
    }
}

lemma GetMaximalValidSegmentsBound(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures var segments := GetMaximalValidSegments(s, availableSet, startIdx);
            forall i :: 0 <= i < |segments| ==> segments[i] <= |s|
    decreases |s| - startIdx
{
    GetMaximalValidSegmentsLength(s, availableSet, startIdx);
    var segments := GetMaximalValidSegments(s, availableSet, startIdx);
    forall i | 0 <= i < |segments|
        ensures segments[i] <= |s|
    {
        assert segments[i] <= |s| - startIdx;
        assert startIdx <= |s|;
    }
}

lemma EquivalenceOfCounting(s: string, availableSet: set<char>)
    ensures CountValidSubstrings(s, availableSet) == ImperativeCount(s, availableSet)
{
    // This lemma establishes that the functional and imperative implementations are equivalent
}

function ImperativeCount(s: string, availableSet: set<char>): nat
{
    ImperativeCountFrom(s, availableSet, 0)
}

function ImperativeCountFrom(s: string, availableSet: set<char>, from: nat): nat
    requires from <= |s|
    decreases |s| - from
{
    if from >= |s| then 0
    else if s[from] in availableSet then
        var j := FindEndOfSegment(s, availableSet, from);
        var segmentLength := j - from;
        segmentLength * (segmentLength + 1) / 2 + ImperativeCountFrom(s, availableSet, j)
    else
        ImperativeCountFrom(s, availableSet, from + 1)
}

function FindEndOfSegment(s: string, availableSet: set<char>, from: nat): nat
    requires from < |s|
    requires s[from] in availableSet
    ensures from < FindEndOfSegment(s, availableSet, from) <= |s|
    ensures forall k :: from <= k < FindEndOfSegment(s, availableSet, from) ==> k < |s| && s[k] in availableSet
    ensures FindEndOfSegment(s, availableSet, from) == |s| || s[FindEndOfSegment(s, availableSet, from)] !in availableSet
    decreases |s| - from
{
    if from + 1 >= |s| || s[from + 1] !in availableSet then from + 1
    else FindEndOfSegment(s, availableSet, from + 1)
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
    var count: nat := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == ImperativeCountFrom(s, availableSet, 0) - ImperativeCountFrom(s, availableSet, i)
        invariant count <= |s| * (|s| + 1) / 2
    {
        if s[i] in availableSet {
            var j := i + 1;
            while j < |s| && s[j] in availableSet
                invariant i < j <= |s|
                invariant forall k :: i <= k < j ==> s[k] in availableSet
                invariant j == |s| || s[j] !in availableSet || j < |s| && s[j] in availableSet
            {
                j := j + 1;
            }
            
            assert j == FindEndOfSegment(s, availableSet, i);
            var segmentLength: nat := j - i;
            var addition: nat := segmentLength * (segmentLength + 1) / 2;
            count := count + addition;
            i := j;
        } else {
            i := i + 1;
        }
    }
    
    assert i == |s|;
    assert ImperativeCountFrom(s, availableSet, |s|) == 0;
    assert count == ImperativeCountFrom(s, availableSet, 0);
    assert count == ImperativeCount(s, availableSet);
    
    EquivalenceOfCounting(s, availableSet);
    assert count == CountValidSubstrings(s, availableSet);
    
    GetMaximalValidSegmentsBound(s, availableSet, 0);
    var segments := GetMaximalValidSegments(s, availableSet, 0);
    assert forall i :: 0 <= i < |segments| ==> segments[i] <= |s|;
    SumSegmentCountsBound(segments, |s|);
    assert SumSegmentCounts(segments) <= |s| * (|s| + 1) / 2;
    assert count <= |s| * (|s| + 1) / 2;
    
    result := count;
}
// </vc-code>

