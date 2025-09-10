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
lemma SegmentCountFormula(n: nat)
    ensures n * (n + 1) / 2 <= n * n
{
    if n <= 1 {
        assert n * (n + 1) / 2 <= n * n;
    } else {
        assert n * (n + 1) / 2 == (n * n + n) / 2;
        assert (n * n + n) / 2 <= n * n;
    }
}

lemma SumSegmentCountsBound(segments: seq<nat>, totalLength: nat)
    requires forall i :: 0 <= i < |segments| ==> segments[i] <= totalLength
    ensures SumSegmentCounts(segments) <= |segments| * totalLength * (totalLength + 1) / 2
{
    if |segments| == 0 {
        assert SumSegmentCounts(segments) == 0;
    } else {
        var first := segments[0];
        assert first <= totalLength;
        assert first * (first + 1) / 2 <= totalLength * (totalLength + 1) / 2;
        SumSegmentCountsBound(segments[1..], totalLength);
    }
}

function SeqToSet(available: seq<char>): set<char>
{
    set c | c in available
}

lemma SeqToSetCorrectness(available: seq<char>, c: char)
    ensures c in SeqToSet(available) <==> c in available
{
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
    
    result := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result <= i * (i + 1) / 2
    {
        if s[i] in availableSet {
            var segmentStart := i;
            var segmentLength := 0;
            
            while i < n && s[i] in availableSet
                invariant segmentStart <= i <= n
                invariant segmentLength == i - segmentStart
            {
                i := i + 1;
                segmentLength := segmentLength + 1;
            }
            
            var segmentCount := segmentLength * (segmentLength + 1) / 2;
            result := result + segmentCount;
        } else {
            i := i + 1;
        }
    }
}
// </vc-code>

