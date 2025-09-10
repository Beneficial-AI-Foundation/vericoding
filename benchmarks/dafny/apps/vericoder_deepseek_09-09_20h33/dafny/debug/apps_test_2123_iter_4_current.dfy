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
  if |s| == 1 {
    // Base case: single element
    assert s[1..] == [];
  } else {
    // Recursive case: the lemma holds by definition
    MaxInSeqTailLemma(s[1..]);
  }
}

lemma MaxInSeqContains(s: seq<int>, x: int)
  requires |s| > 0 && x in s
  ensures x <= MaxInSeq(s)
{
  if |s| == 1 {
    // Base case: single element
    assert s[0] == x && MaxInSeq(s) == s[0];
  } else {
    if x == s[0] {
      // x is the first element
      var tailMax := MaxInSeq(s[1..]);
      if s[0] >= tailMax {
        assert MaxInSeq(s) == s[0];
      } else {
        assert s[0] <= tailMax;
        assert MaxInSeq(s) == tailMax;
      }
    } else {
      // x is in the tail
      MaxInSeqContains(s[1..], x);
      var tailMax := MaxInSeq(s[1..]);
      assert x <= tailMax;
      if s[0] >= tailMax {
        assert MaxInSeq(s) == s[0];
        assert tailMax <= s[0];
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
  assert extended[0] == prev[0];
  assert extended[1..] == prev[1..] + [newElem];
  
  if |prev| == 1 {
    if newElem > prev[0] {
      assert MaxInSeq(extended) == newElem;
    } else {
      assert MaxInSeq(extended) == prev[0];
    }
  } else {
    var tailMax := MaxInSeq(prev[1..] + [newElem]);
    MaxInSeqExtensionLemma(prev[1..], newElem);
    if prev[0] >= tailMax {
      assert MaxInSeq(extended) == prev[0];
    } else {
      assert MaxInSeq(extended) == tailMax;
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
  var maxSoFar := heights[0];
  var idx := 1;
  
  while idx < n
    invariant 1 <= idx <= n
    invariant maxSoFar in heights[0..idx]
    invariant forall j :: 0 <= j < idx ==> heights[j] <= maxSoFar
    invariant exists j :: 0 <= j < idx && heights[j] == maxSoFar
    invariant maxSoFar == MaxInSeq(heights[0..idx])
  {
    var prevSlice := heights[0..idx];
    var newSlice := heights[0..idx+1];
    
    // Update maxSoFar
    if heights[idx] > maxSoFar {
      maxSoFar := heights[idx];
    }
    
    // Prove the invariant for the next iteration
    assert |prevSlice| > 0;  // Since idx >= 1, at least heights[0] is present
    MaxInSeqExtensionLemma(prevSlice, heights[idx]);
    assert MaxInSeq(newSlice) == (if heights[idx] > MaxInSeq(prevSlice) then heights[idx] else MaxInSeq(prevSlice));
    
    idx := idx + 1;
  }
  result := maxSoFar;
}
// </vc-code>

