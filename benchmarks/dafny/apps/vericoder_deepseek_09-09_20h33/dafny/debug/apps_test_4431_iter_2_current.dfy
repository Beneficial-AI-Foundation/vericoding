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
    ensures SumSegmentCounts(segments) <= SumSegmentCounts(segments[..|segments|-1]) + (if |segments| > 0 then segments[|segments|-1] * (segments[|segments|-1] + 1) / 2 else 0)
{
    // This lemma remains as a placeholder for the verification
}

lemma GetMaximalValidSegmentsLemma(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures |GetMaximalValidSegments(s, availableSet, startIdx)| <= |s| - startIdx
{
    // This lemma remains as a placeholder for the verification
}

lemma GetNextSegmentLengthLemma(s: string, availableSet: set<char>, startIdx: nat)
    requires startIdx <= |s|
    ensures GetNextSegmentLength(s, availableSet, startIdx) <= |s| - startIdx
{
    // This lemma remains as a placeholder for the verification
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
        invariant total <= i * (i + 1) / 2
    {
        var j := i;
        var currentCount := 0;
        
        while j < n && s[j] in availableSet
            invariant i <= j <= n
            invariant currentCount == j - i
            invariant total == (if j > i then (j - i) * (j - i + 1) / 2 else 0)
        {
            currentCount := currentCount + 1;
            total := total + currentCount;
            j := j + 1;
        }
        
        if j == n {
            break;
        }
        
        i := j + 1;
    }
    
    result := total;
}
// </vc-code>

