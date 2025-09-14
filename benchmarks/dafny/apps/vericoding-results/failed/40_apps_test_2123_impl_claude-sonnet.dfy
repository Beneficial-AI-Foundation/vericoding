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
lemma MaxInSeqProperties(s: seq<int>)
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s)
{
    if |s| == 1 {
        assert s[0] == MaxInSeq(s);
        assert MaxInSeq(s) in s;
        assert exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s);
    } else {
        MaxInSeqProperties(s[1..]);
        var tailMax := MaxInSeq(s[1..]);
        if s[0] >= tailMax {
            assert MaxInSeq(s) == s[0];
            assert exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s);
        } else {
            assert MaxInSeq(s) == tailMax;
            assert exists j :: 0 <= j < |s[1..]| && s[1..][j] == tailMax;
            assert exists i :: 0 <= i < |s| && s[i] == MaxInSeq(s);
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
    MaxInSeqProperties(heights);
    result := MaxInSeq(heights);
}
// </vc-code>

