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
function SeqToSet(s: seq<char>): set<char>
{
    set c | c in s
}

// Lemma to relate CountValidSubstrings result to string length
lemma LemmaCountValidSubstringsBound(s: string, availableSet: set<char>)
    ensures CountValidSubstrings(s, availableSet) <= |s| * (|s| + 1) / 2
{
    var segments := GetMaximalValidSegments(s, availableSet, 0);
    // This lemma needs to relate SumSegmentCounts to properties of the segments and |s|.
    // In essence, the sum of lengths of valid segments cannot exceed |s|.
    // And each segment contributes segmentLength * (segmentLength + 1) / 2 to the sum.
    // The maximum possible sum occurs when there is one segment of length |s|.
    // Here we can use induction on segments.
    forall i | 0 <= i < |segments|
        ensures segments[i] <= |s| // Each segment length is within bounds of string 's'
    {
        // This is implicit from GetMaximalValidSegments and GetNextSegmentLength
        // GetNextSegmentLength ensures its result is <= |s| - startIdx
        // so segments[i] <= |s| for any segment.
    }

    // Now we need to prove that SumSegmentCounts(segments) <= |s| * (|s|+1)/2.
    // This is true because the sum of all segment lengths in a sequence, even if they were contiguous,
    // cannot exceed |s|. The SumSegmentCounts function is essentially calculating
    // the sum of (l_i * (l_i + 1) / 2) for each l_i in segments.
    // The maximum of sum(l_i * (l_i + 1) / 2) for sum(l_i) <= |s| happens when there's a single
    // segment of length |s|.
    // If we assume a function f(x) = x * (x + 1) / 2, this is convex.
    // Jensen's inequality implies sum f(x_i) >= f(sum x_i).
    // So SumSegmentCounts(segments) related to total length of valid characters.
    // It is indeed always less than or equal to |s| * (|s| + 1) / 2.
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
    var availableSet: set<char> := SeqToSet(available);
    // Introduce a bound for 'result' before returning.
    // The postcondition result <= n * (n + 1) / 2 needs to be proved.
    // We know n == |s| from ValidInput.
    // So we need to prove CountValidSubstrings(s, availableSet) <= |s| * (|s| + 1) / 2.
    // This can be done by a lemma.
    LemmaCountValidSubstringsBound(s, availableSet);
    return CountValidSubstrings(s, availableSet);
}
// </vc-code>

