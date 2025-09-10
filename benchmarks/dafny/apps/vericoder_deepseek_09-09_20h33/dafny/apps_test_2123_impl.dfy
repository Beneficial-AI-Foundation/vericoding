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
lemma MaxInSeqTailLemma(s: seq<int>)
  requires |s| > 0
  ensures MaxInSeq(s) == (if s[0] >= MaxInSeq(s[1..]) then s[0] else MaxInSeq(s[1..]))
{
  // The lemma holds by the definition of MaxInSeq
}

lemma MaxInSeqContains(s: seq<int>, x: int)
  requires |s| > 0 && x in s
  ensures x <= MaxInSeq(s)
{
  if |s| == 1 {
    assert s[0] == x && MaxInSeq(s) == s[0];
  } else {
    if x == s[0] {
      var tailMax := MaxInSeq(s[1..]);
      if s[0] >= tailMax {
        assert MaxInSeq(s) == s[0];
      } else {
        assert s[0] <= tailMax;
        assert MaxInSeq(s) == tailMax;
      }
    } else {
      MaxInSeqContains(s[1..], x);
      var tailMax := MaxInSeq(s[1..]);
      assert x <= tailMax;
      if s[0] >= tailMax {
        assert tailMax <= s[0];
        assert MaxInSeq(s) == s[0];
      } else {
        assert MaxInSeq(s) == tailMax;
      }
    }
  }
}

lemma MaxInSeqTailDecreases(s: seq<int>)
  requires |s| > 1
  ensures |s[1..]| > 0
{
  assert |s[1..]| == |s| - 1 > 0;
}

lemma MaxInSeqExtensionLemma(prev: seq<int>, newElem: int)
  requires |prev| > 0
  ensures MaxInSeq(prev + [newElem]) == (if newElem > MaxInSeq(prev) then newElem else MaxInSeq(prev))
{
  var extended := prev + [newElem];
  MaxInSeqTailLemma(extended);
  
  if |prev| == 1 {
    if newElem > prev[0] {
      assert MaxInSeq(extended) == newElem;
    } else {
      assert MaxInSeq(extended) == prev[0];
    }
  } else {
    var tailExtended := prev[1..] + [newElem];
    MaxInSeqExtensionLemma(prev[1..], newElem);
    var tailMax := MaxInSeq(tailExtended);
    
    if prev[0] >= tailMax {
      assert MaxInSeq(extended) == prev[0];
    } else {
      assert MaxInSeq(extended) == tailMax;
    }
  }
}

lemma MaxInSeqSliceLemma(s: seq<int>, start: int, end: int)
  requires 0 <= start < end <= |s|
  ensures |s[start..end]| > 0
{
  assert end - start > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
{
  var maxSoFar := heights[0];
  var idx := 1;
  
  while idx < n
    invariant 1 <= idx <= n
    invariant maxSoFar in heights[0..idx]
    invariant forall j :: 0 <= j < idx ==> heights[j] <= maxSoFar
    invariant exists j :: 0 <= j < idx && heights[j] == maxSoFar
    invariant maxSoFar == MaxInSeq(heights[0..idx])
  {
    MaxInSeqSliceLemma(heights, 0, idx);
    assert |heights[0..idx]| > 0;
    
    MaxInSeqExtensionLemma(heights[0..idx], heights[idx]);
    
    if heights[idx] > maxSoFar {
      maxSoFar := heights[idx];
    }
    
    idx := idx + 1;
  }
  result := maxSoFar;
}
// </vc-code>

