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
/* helper modified by LLM (iteration 3): Added loop invariants to help prove the postcondition for MaximalMatches */
method FindMaximalMatches(s: string, sub: string, start: int, endPos: int) returns (positions: seq<int>)
  ensures MaximalMatches(s, sub, positions, start, endPos)
{
  var current := start;
  var posSeq := [];
  while current + |sub| <= endPos
    invariant NonOverlapping(posSeq, |sub|)
    invariant current >= start && current <= endPos
    invariant forall p :: p in posSeq ==> start <= p && p + |sub| <= endPos && SubstringAt(s, sub, p)
    decreases endPos - current
  {
    if SubstringAt(s, sub, current)
    {
      posSeq := posSeq + [current];
      current := current + |sub|;
    }
    else
    {
      current := current + 1;
    }
  }
  positions := posSeq;
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
  /* code modified by LLM (iteration 3): Used for loop to iterate over indices for clearer verification */
  result := [];
  for i := 0 to |a| - 1
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] >= 0
  {
    var pos := FindMaximalMatches(a[i], sub[i], start[i], endPos[i]);
    result := result + [|pos|];
  }
}
// </vc-code>
