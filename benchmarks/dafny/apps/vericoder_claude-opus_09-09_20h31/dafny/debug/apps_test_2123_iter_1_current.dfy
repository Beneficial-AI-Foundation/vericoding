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
lemma MaxInSeqProperties(s: seq<int>, i: int)
    requires |s| > 0
    requires 0 <= i < |s|
    ensures s[i] <= MaxInSeq(s)
{
    // This follows from the postcondition of MaxInSeq
}

lemma MaxInSeqIsMax(s: seq<int>)
    requires |s| > 0
    ensures exists j :: 0 <= j < |s| && s[j] == MaxInSeq(s)
{
    // This follows from the postcondition of MaxInSeq that MaxInSeq(s) in s
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
{
    var maxVal := heights[0];
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant maxVal in heights[0..i]
        invariant forall j :: 0 <= j < i ==> heights[j] <= maxVal
        invariant exists j :: 0 <= j < i && heights[j] == maxVal
    {
        if heights[i] > maxVal {
            maxVal := heights[i];
        }
        i := i + 1;
    }
    
    assert i == n;
    assert maxVal in heights[0..n];
    assert heights == heights[0..n];
    assert maxVal in heights;
    assert forall j :: 0 <= j < n ==> heights[j] <= maxVal;
    assert exists j :: 0 <= j < n && heights[j] == maxVal;
    
    // Prove that maxVal == MaxInSeq(heights)
    assert forall j :: 0 <= j < |heights| ==> heights[j] <= maxVal;
    assert maxVal in heights;
    assert maxVal == MaxInSeq(heights);
    
    result := maxVal;
}
// </vc-code>

