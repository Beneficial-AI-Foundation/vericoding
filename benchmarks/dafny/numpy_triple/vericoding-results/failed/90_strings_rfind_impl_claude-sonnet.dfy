// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proper triggers and strengthened postconditions */
method findRightmostOccurrence(s: string, sub: string, start: int, endPos: int) returns (result: int)
  requires 0 <= start
  requires start <= endPos
  ensures result == -1 || (start <= result && result + |sub| <= endPos + 1 && result + |sub| <= |s|)
  ensures result != -1 ==> s[result..result+|sub|] == sub
  ensures result != -1 ==> forall j {:trigger s[j..j+|sub|]} :: result < j && start <= j && j + |sub| <= endPos + 1 && j + |sub| <= |s| ==> s[j..j+|sub|] != sub
  ensures result == -1 ==> forall j {:trigger s[j..j+|sub|]} :: start <= j && j + |sub| <= endPos + 1 && j + |sub| <= |s| ==> s[j..j+|sub|] != sub
{
  var maxPos := if endPos + 1 - |sub| >= 0 then endPos + 1 - |sub| else -1;
  if maxPos < start || maxPos + |sub| > |s| {
    result := -1;
    return;
  }
  
  var pos := maxPos;
  while pos >= start
    invariant pos >= start - 1
    invariant forall j {:trigger s[j..j+|sub|]} :: pos < j <= maxPos && start <= j && j + |sub| <= endPos + 1 && j + |sub| <= |s| ==> s[j..j+|sub|] != sub
    decreases pos - start + 1
  {
    if pos + |sub| <= |s| && s[pos..pos+|sub|] == sub {
      result := pos;
      return;
    }
    pos := pos - 1;
  }
  result := -1;
}
// </vc-helpers>

// <vc-spec>
method rfind(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) returns (result: seq<int>)
  // All input sequences must have the same length
  requires |a| == |sub| == |start| == |endPos|
  // Start positions must be non-negative and not exceed end positions
  requires forall i :: 0 <= i < |start| ==> 0 <= start[i] <= endPos[i]
  // Result sequence has same length as inputs
  ensures |result| == |a|
  // For each element i, the result satisfies the rfind specification
  ensures forall i :: 0 <= i < |result| ==> 
    // Result is either -1 or a valid index within the string
    (result[i] == -1 || (0 <= result[i] < |a[i]|)) &&
    
    // If result is -1, then no occurrence of substring exists within the specified range
    (result[i] == -1 ==> 
      (forall j {:trigger a[i][j..j+|sub[i]|]} :: start[i] <= j && j + |sub[i]| <= endPos[i] + 1 && j + |sub[i]| <= |a[i]| ==>
        a[i][j..j+|sub[i]|] != sub[i])) &&
    
    // If result is non-negative, it represents the rightmost valid occurrence
    (result[i] >= 0 ==> 
      // The result position is within the search range
      start[i] <= result[i] && 
      result[i] + |sub[i]| <= endPos[i] + 1 &&
      // The result position is valid within the string bounds  
      result[i] + |sub[i]| <= |a[i]| &&
      // The substring matches at the result position
      a[i][result[i]..result[i]+|sub[i]|] == sub[i] &&
      // This is the rightmost occurrence - no later occurrence exists in the range
      (forall j {:trigger a[i][j..j+|sub[i]|]} :: (result[i] < j && j + |sub[i]| <= endPos[i] + 1 && 
                   start[i] <= j && j + |sub[i]| <= |a[i]|) ==> 
        a[i][j..j+|sub[i]|] != sub[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added proper triggers to match postcondition specification */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
      (result[k] == -1 || (0 <= result[k] < |a[k]|)) &&
      (result[k] == -1 ==> 
        (forall j {:trigger a[k][j..j+|sub[k]|]} :: start[k] <= j && j + |sub[k]| <= endPos[k] + 1 && j + |sub[k]| <= |a[k]| ==> a[k][j..j+|sub[k]|] != sub[k])) &&
      (result[k] >= 0 ==> 
        start[k] <= result[k] && 
        result[k] + |sub[k]| <= endPos[k] + 1 &&
        result[k] + |sub[k]| <= |a[k]| &&
        a[k][result[k]..result[k]+|sub[k]|] == sub[k] &&
        (forall j {:trigger a[k][j..j+|sub[k]|]} :: (result[k] < j && j + |sub[k]| <= endPos[k] + 1 && start[k] <= j && j + |sub[k]| <= |a[k]|) ==> a[k][j..j+|sub[k]|] != sub[k]))
  {
    var pos := findRightmostOccurrence(a[i], sub[i], start[i], endPos[i]);
    result := result + [pos];
    i := i + 1;
  }
}
// </vc-code>
