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
/* helper modified by LLM (iteration 5): The `FindNextNonOverlapping` function needs to correctly return `endPos + 1` if no match is found, to align with the typical search pattern where the search continues from `p + 1`. This also means the loop condition for the `while` should be `p < endPos`, to correctly iterate through all possible starting positions up to `endPos - |sub|`. The `p <= endPos` was one past, and `p + |sub| <= endPos` was a bit too restrictive. Correcting the return value and the loop condition for finding the *next* possible non-overlapping match. */
function FindNextNonOverlapping(s: string, sub: string, currentPos: int, endPos: int): (nextMatch: int)
  requires 0 <= currentPos <= endPos <= |s|
  requires |sub| > 0
{
  var p := currentPos;
  while p + |sub| <= endPos
    invariant currentPos <= p
    invariant forall k :: currentPos <= k < p ==> !SubstringAt(s, sub, k)
    decreases endPos - p
  {
    if SubstringAt(s, sub, p) then
      return p;
    p := p + 1;
  }
  return endPos + 1; // Return endPos + 1 if no match found within the range
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
/* code modified by LLM (iteration 5): Adjusted the 'while' loop condition for `currentSearchPos` to use `currentSearchPos <= end_pos - |sub_str|`, which accurately signifies when a full substring can still fit within the `end_pos` boundary. Previously, the condition `currentSearchPos + |sub_str| <= end_pos` was causing issues with identifying the exact conditions for the last possible match. This change prevents out-of-bounds checks and correctly processes all potential matches. The return value from `FindNextNonOverlapping` (which is `endPos + 1` when no match is found) is now correctly handled to terminate the loop. */
{
  result := new int[|a|];
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
  {
    var currentCount := 0;
    var currentSearchPos := start[i];
    var s := a[i];
    var sub_str := sub[i];
    var end_pos := endPos[i];

    if |sub_str| > end_pos - currentSearchPos then
      currentCount := 0;
    else
      while currentSearchPos <= end_pos - |sub_str|
        invariant start[i] <= currentSearchPos <= end_pos + 1
        invariant currentCount >= 0
      {
        var nextMatchPos := FindNextNonOverlapping(s, sub_str, currentSearchPos, end_pos);
        if nextMatchPos >= end_pos + 1 then // No more matches found
          break;
        currentCount := currentCount + 1;
        currentSearchPos := nextMatchPos + |sub_str|;
      }
    result[i] := currentCount;
  }
}
// </vc-code>
