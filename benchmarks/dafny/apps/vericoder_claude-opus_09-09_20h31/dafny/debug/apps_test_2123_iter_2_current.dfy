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
    assert MaxInSeq(s) in s;
}

lemma MaxValueIsMaxInSeq(s: seq<int>, maxVal: int)
    requires |s| > 0
    requires maxVal in s
    requires forall j :: 0 <= j < |s| ==> s[j] <= maxVal
    ensures maxVal == MaxInSeq(s)
{
    var m := MaxInSeq(s);
    assert m in s;
    assert forall j :: 0 <= j < |s| ==> s[j] <= m;
    
    // Since maxVal is in s, we have maxVal <= m
    var idx :| 0 <= idx < |s| && s[idx] == maxVal;
    assert s[idx] <= m;
    assert maxVal <= m;
    
    // Since all elements <= maxVal and m is in s, we have m <= maxVal
    var midx :| 0 <= midx < |s| && s[midx] == m;
    assert s[midx] <= maxVal;
    assert m <= maxVal;
    
    // Therefore maxVal == m
    assert maxVal == m;
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
    MaxValueIsMaxInSeq(heights, maxVal);
    assert maxVal == MaxInSeq(heights);
    
    // Now we can establish the postcondition
    MaxInSeqIsMax(heights);
    assert exists j :: 0 <= j < |heights| && heights[j] == MaxInSeq(heights);
    
    result := maxVal;
}
// </vc-code>

