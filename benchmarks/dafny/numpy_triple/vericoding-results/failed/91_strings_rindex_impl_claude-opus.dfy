// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error with such-that operator */
function FindLastIndex(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos <= |s|
  requires exists j :: start <= j && j + |sub| <= |s| && j <= endPos && (|sub| == 0 || s[j..j+|sub|] == sub)
  ensures start <= FindLastIndex(s, sub, start, endPos) <= endPos
  ensures FindLastIndex(s, sub, start, endPos) + |sub| <= |s|
  ensures |sub| == 0 || s[FindLastIndex(s, sub, start, endPos)..FindLastIndex(s, sub, start, endPos)+|sub|] == sub
  ensures forall j :: FindLastIndex(s, sub, start, endPos) < j <= endPos && j + |sub| <= |s| ==> |sub| == 0 || s[j..j+|sub|] != sub
{
  if |sub| == 0 then
    endPos
  else
    var candidates := set j | start <= j <= endPos && j + |sub| <= |s| && s[j..j+|sub|] == sub;
    var witness :| witness in candidates;
    var maxIdx :| maxIdx in candidates && forall k :: k in candidates ==> k <= maxIdx;
    maxIdx
}
// </vc-helpers>

// <vc-spec>
method rindex(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) returns (result: seq<int>)
  // All input sequences must have the same length
  requires |a| == |sub| == |start| == |endPos|
  
  // For each string, validate range bounds and ensure substring exists
  requires forall i :: 0 <= i < |a| ==>
    // Valid range bounds: start <= end <= string length
    0 <= start[i] <= endPos[i] <= |a[i]| &&
    
    // Substring must exist within the specified range (key precondition for rindex)
    exists j {:trigger a[i][j..j+|sub[i]|]} :: start[i] <= j && 
                j + |sub[i]| <= |a[i]| &&
                j <= endPos[i] &&
                (|sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i])

  // Result sequence has same length as input sequences  
  ensures |result| == |a|
  
  // For each result index, verify correctness properties
  ensures forall i :: 0 <= i < |result| ==>
    // Result is always non-negative (no -1 values like rfind)
    result[i] >= 0 &&
    
    // Result is within the valid search range
    start[i] <= result[i] &&
    result[i] <= endPos[i] &&
    
    // The substring is found at the returned index
    result[i] + |sub[i]| <= |a[i]| &&
    (|sub[i]| == 0 || a[i][result[i]..result[i]+|sub[i]|] == sub[i]) &&
    
    // This is the highest (rightmost) valid index where substring is found in range
    (forall j {:trigger a[i][j..j+|sub[i]|]} :: result[i] < j <= endPos[i] && j + |sub[i]| <= |a[i]| ==>
      |sub[i]| == 0 || a[i][j..j+|sub[i]|] != sub[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implementation using FindLastIndex helper */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==>
      result[k] >= 0 &&
      start[k] <= result[k] &&
      result[k] <= endPos[k] &&
      result[k] + |sub[k]| <= |a[k]| &&
      (|sub[k]| == 0 || a[k][result[k]..result[k]+|sub[k]|] == sub[k]) &&
      (forall j :: result[k] < j <= endPos[k] && j + |sub[k]| <= |a[k]| ==> |sub[k]| == 0 || a[k][j..j+|sub[k]|] != sub[k])
  {
    assert exists j :: start[i] <= j && j + |sub[i]| <= |a[i]| && j <= endPos[i] && (|sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i]);
    var idx := FindLastIndex(a[i], sub[i], start[i], endPos[i]);
    result := result + [idx];
    i := i + 1;
  }
}
// </vc-code>
