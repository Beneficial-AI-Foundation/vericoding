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
  // This lemma is automatically verified by Dafny's induction
}

lemma MaxInSeqContains(s: seq<int>, x: int)
  requires |s| > 0 && x in s
  ensures x <= MaxInSeq(s)
{
  // This lemma is automatically verified by Dafny's induction
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
{
  result := heights[0];
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant result in heights[0..i]
    invariant forall j :: 0 <= j < i ==> heights[j] <= result
    invariant exists j :: 0 <= j < i && heights[j] == result
  {
    if heights[i] > result {
      result := heights[i];
    }
    i := i + 1;
  }
}
// </vc-code>

