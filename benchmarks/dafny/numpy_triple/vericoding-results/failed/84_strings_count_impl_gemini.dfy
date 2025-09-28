// <vc-preamble>
// Predicate to check if a substring occurs at a specific position in a string
predicate SubstringAt(s: string, sub: string, pos: int)
{
  pos >= 0 && pos + |sub| <= |s| && s[pos..pos + |sub|] == sub
}

// Predicate to check if positions are non-overlapping for a given substring length
predicate NonOverlapping(positions: seq<int>, subLen: int)
{
  forall i, j :: 0 <= i < j < |positions| ==> positions[i] + subLen <= positions[j]
}

// Predicate to check if all positions are valid matches within the range
predicate ValidMatches(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
{
  forall pos :: pos in positions ==> 
    start <= pos && pos + |sub| <= endPos && SubstringAt(s, sub, pos)
}

// Predicate to check if a set of positions represents the maximum non-overlapping count
ghost predicate MaximalMatches(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
{
  ValidMatches(s, sub, positions, start, endPos) &&
  NonOverlapping(positions, |sub|) &&
  forall otherPositions :: 
    |otherPositions| <= (endPos - start) &&
    (forall pos :: pos in otherPositions ==> start <= pos && pos + |sub| <= endPos) &&
    (ValidMatches(s, sub, otherPositions, start, endPos) && NonOverlapping(otherPositions, |sub|)) ==>
    |otherPositions| <= |positions|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): explicitly named the return value to fix compilation error */
ghost function FindFirstOccurrence(s: string, sub: string, start: int, end_limit: int): (result: int)
  requires 0 <= start <= end_limit <= |s|
  requires |sub| > 0
  ensures -1 <= result
  ensures result != -1 ==> start <= result && result + |sub| <= end_limit && SubstringAt(s, sub, result)
  ensures result != -1 ==> forall i :: start <= i < result ==> !SubstringAt(s, sub, i)
  ensures result == -1 ==> forall i :: start <= i <= end_limit - |sub| ==> !SubstringAt(s, sub, i)
  decreases end_limit - start
{
  if start + |sub| > end_limit then -1
  else if SubstringAt(s, sub, start) then start
  else FindFirstOccurrence(s, sub, start + 1, end_limit)
}

/* helper modified by LLM (iteration 4): explicitly named the return value to fix compilation error */
ghost function GetGreedyPositions(s: string, sub: string, start: int, end_limit: int): (result: seq<int>)
  requires 0 <= start <= end_limit <= |s|
  requires |sub| > 0
  ensures ValidMatches(s, sub, result, start, end_limit)
  ensures NonOverlapping(result, |sub|)
  ensures |result| > 0 ==> result[0] == FindFirstOccurrence(s, sub, start, end_limit)
  decreases end_limit - start
{
  if start + |sub| > end_limit then
    []
  else
    var p := FindFirstOccurrence(s, sub, start, end_limit);
    if p == -1 then
      []
    else
      [p] + GetGreedyPositions(s, sub, p + |sub|, end_limit)
}

lemma lemma_GreedyVsOther(s: string, sub: string, start: int, end_limit: int, other: seq<int>)
  requires 0 <= start <= end_limit <= |s|
  requires |sub| > 0
  requires ValidMatches(s, sub, other, start, end_limit)
  requires NonOverlapping(other, |sub|)
  ensures |other| <= |GetGreedyPositions(s, sub, start, end_limit)|
  decreases |other|
{
  var greedy := GetGreedyPositions(s, sub, start, end_limit);
  if |other| > 0 {
    var p := FindFirstOccurrence(s, sub, start, end_limit);
    if p == -1 {
      assert forall i :: start <= i <= end_limit - |sub| ==> !SubstringAt(s, sub, i);
      var o0 := other[0];
      assert SubstringAt(s, sub, o0) && start <= o0 && o0 + |sub| <= end_limit;
    } else {
      assert |greedy| > 0 && greedy[0] == p;
      var o0 := other[0];
      assert p <= o0;
      var other_rest := other[1..];
      lemma_GreedyVsOther(s, sub, p + |sub|, end_limit, other_rest);
    }
  }
}

/* helper modified by LLM (iteration 3): fixed syntax for ghost return parameter */
method ComputeSingle(s: string, sub: string, start: int, endPos: int)
    returns (count: int, ghost final_positions: seq<int>)
  requires 0 <= start <= endPos <= |s|
  requires |sub| > 0
  ensures count >= 0
  ensures |sub| > endPos - start ==> count == 0
  ensures |final_positions| == count
  ensures MaximalMatches(s, sub, final_positions, start, endPos)
{
    if |sub| > endPos - start {
        return 0, [];
    }
    final_positions := GetGreedyPositions(s, sub, start, endPos);
    count := |final_positions|;
    
    assert ValidMatches(s, sub, final_positions, start, endPos);
    assert NonOverlapping(final_positions, |sub|);

    forall other |
        |other| <= (endPos - start) &&
        (forall pos :: pos in other ==> start <= pos && pos + |sub| <= endPos) &&
        ValidMatches(s, sub, other, start, endPos) &&
        NonOverlapping(other, |sub|)
    ensures |other| <= |final_positions|
    {
        lemma_GreedyVsOther(s, sub, start, endPos, other);
    }
}
// </vc-helpers>

// <vc-spec>
method Count(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) 
  returns (result: seq<int>)
  requires |a| == |sub| == |start| == |endPos|
  requires forall i :: 0 <= i < |a| ==> start[i] <= endPos[i]
  requires forall i :: 0 <= i < |a| ==> 0 <= start[i] <= |a[i]|
  requires forall i :: 0 <= i < |a| ==> 0 <= endPos[i] <= |a[i]|
  requires forall i :: 0 <= i < |a| ==> |sub[i]| > 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] >= 0
  ensures forall i :: 0 <= i < |a| ==> 
    (|sub[i]| > endPos[i] - start[i] ==> result[i] == 0)
  ensures forall i :: 0 <= i < |a| ==>
    exists positions :: 
      |positions| == result[i] &&
      MaximalMatches(a[i], sub[i], positions, start[i], endPos[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): no changes; fixed compilation errors in helpers */
  result := [];
  var i := 0;
  while i < |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    invariant forall j :: 0 <= j < i ==> 
      (|sub[j]| > endPos[j] - start[j] ==> result[j] == 0)
    invariant forall j :: 0 <= j < i ==>
      exists positions :: 
        |positions| == result[j] &&
        MaximalMatches(a[j], sub[j], positions, start[j], endPos[j])
  {
    var count_i: int;
    ghost var positions_i: seq<int>;
    count_i, positions_i := ComputeSingle(a[i], sub[i], start[i], endPos[i]);
    result := result + [count_i];
    i := i + 1;
  }
}
// </vc-code>
