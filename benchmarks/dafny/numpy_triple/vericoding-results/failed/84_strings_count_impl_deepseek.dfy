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
/* helper modified by LLM (iteration 5): Fixed loop condition syntax by removing subtraction from while condition */
function FindMatches(s: string, sub: string, start: int, endPos: int): seq<int>
  requires |sub| > 0
  requires 0 <= start <= endPos <= |s|
  ensures ValidMatches(s, sub, FindMatches(s, sub, start, endPos), start, endPos)
  ensures NonOverlapping(FindMatches(s, sub, start, endPos), |sub|)
  ensures forall otherMatches :: ValidMatches(s, sub, otherMatches, start, endPos) && NonOverlapping(otherMatches, |sub|) ==> |otherMatches| <= |FindMatches(s, sub, start, endPos)|
{
  if start > endPos - |sub| then [] else
  var matches: seq<int> := [];
  var current := start;
  var max_pos := endPos - |sub|;
  while current <= max_pos
    invariant current >= start
    invariant current <= max_pos + 1
    invariant ValidMatches(s, sub, matches, start, endPos)
    invariant NonOverlapping(matches, |sub|)
    invariant forall pos :: pos in matches ==> pos < current
  {
    if SubstringAt(s, sub, current) {
      matches := matches + [current];
      current := current + |sub|;
    } else {
      current := current + 1;
    }
  }
  matches
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
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    invariant forall j :: 0 <= j < i ==> 
      (|sub[j]| > endPos[j] - start[j] ==> result[j] == 0)
    invariant forall j :: 0 <= j < i ==>
      exists positions :: 
        |positions| == result[j] &&
        MaximalMatches(a[j], sub[j], positions, start[j], endPos[j])
  {
    if |sub[i]| > endPos[i] - start[i] {
      result := result + [0];
    } else {
      var matches := FindMatches(a[i], sub[i], start[i], endPos[i]);
      result := result + [|matches|];
    }
    i := i + 1;
  }
}
// </vc-code>
