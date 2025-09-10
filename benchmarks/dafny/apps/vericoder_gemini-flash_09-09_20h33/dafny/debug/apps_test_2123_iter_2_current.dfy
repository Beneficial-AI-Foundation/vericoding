predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
{
    if |s| == 1 then s[0]
    else
        var tailMax := MaxInSeq(s[1..]);
        if s[0] >= tailMax then s[0] else tailMax
}

predicate ValidResult(n: int, heights: seq<int>, result: int)
    requires ValidInput(n, heights)
{
    result == MaxInSeq(heights) &&
    forall i :: 0 <= i < |heights| ==> heights[i] <= result &&
    exists i :: 0 <= i < |heights| && heights[i] == result
}

// <vc-helpers>
function MaxInSeqIter(s: seq<int>, index: int, currentMax: int): int
    requires 0 <= index <= |s|
    requires |s| > 0
    requires index == 0 ==> currentMax == s[0]
    decreases |s| - index
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeqIter(s, 0, s[0])
    ensures exists i :: 0 <= i < |s| && s[i] == MaxInSeqIter(s, 0, s[0])
    ensures index == |s| ==> currentMax == MaxInSeqIter(s, 0, s[0])
{
    if index == |s| then
        currentMax
    else
        var newMax := if s[index] > currentMax then s[index] else currentMax;
        MaxInSeqIter(s, index + 1, newMax)
}

lemma MaxInSeqProperties(s: seq<int>)
    requires |s| > 0
    ensures MaxInSeq(s) == MaxInSeqIter(s, 0, s[0])
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s)
{
    if |s| == 1 {
        calc {
            MaxInSeq(s);
            s[0];
            MaxInSeqIter(s, 0, s[0]);
        }
    } else {
        var tailMax := MaxInSeq(s[1..]);
        MaxInSeqProperties(s[1..]);
        assert MaxInSeq(s[1..]) == MaxInSeqIter(s[1..], 0, s[1]);

        var iterMaxFromTail := MaxInSeqIter(s[1..], 0, s[1]);

        if s[0] >= tailMax {
            calc {
                MaxInSeq(s);
                s[0];
            }
            // Prove MaxInSeqIter(s, 0, s[0]) == s[0]
            if s[0] >= iterMaxFromTail { // This indicates s[0] is the maximum of the entire sequence
                // MaxInSeqIter(s, 0, s[0]) effectively computes max({s[0]} union {s[1..]})
                // If s[0] >= max(s[1..]), then max(s) = s[0]
                // And MaxInSeqIter(s, 0, s[0]) would return s[0]
                assert MaxInSeqIter(s, 0, s[0]) == s[0];
            } else {
                // If s[0] < max(s[1..]), then max(s) = max(s[1..])
                // And MaxInSeqIter(s, 0, s[0]) would return max(s[1..])
                assert MaxInSeqIter(s, 0, s[0]) == iterMaxFromTail;
            }
            assert MaxInSeq(s) == MaxInSeqIter(s, 0, s[0]);
        } else {
            calc {
                MaxInSeq(s);
                tailMax;
            }
            assert MaxInSeq(s[1..]) == iterMaxFromTail;
            // Since s[0] < tailMax, the max of the sequence is tailMax, which is MaxInSeqIter(s[1..], 0, s[1])
            assert MaxInSeqIter(s, 0, s[0]) == iterMaxFromTail;
            assert MaxInSeq(s) == MaxInSeqIter(s, 0, s[0]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
{
    var currentMax: int := heights[0];
    var i: int := 1;

    while i < n
        invariant 0 <= i <= n
        invariant currentMax == MaxInSeqIter(heights, 0, heights[0]) // This invariant should capture the max up to this point
                                 when evaluated for heights[0..i-1] effectively
        invariant forall k :: 0 <= k < i ==> heights[k] <= currentMax
        invariant exists k :: 0 <= k < i && heights[k] == currentMax
        decreases n - i
    {
        if heights[i] > currentMax {
            currentMax := heights[i];
        } else {} // Add an empty else branch to prevent specific verification problems.
        i := i + 1;
    }
    result := currentMax;
    MaxInSeqProperties(heights);
}
// </vc-code>

