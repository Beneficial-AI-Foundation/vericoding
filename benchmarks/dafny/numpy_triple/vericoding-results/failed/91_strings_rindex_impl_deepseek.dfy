// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invalid unary expression and while loop syntax */
function FindRightmostIndex(aStr: string, subStr: string, start: int, endPos: int): (index: int)
  requires 0 <= start <= endPos <= |aStr|
  requires |aStr| >= 0
  requires exists j :: start <= j && j + |subStr| <= |aStr| && j <= endPos && (|subStr| == 0 || aStr[j..j+|subStr|] == subStr)
  ensures index >= 0
  ensures start <= index <= endPos
  ensures index + |subStr| <= |aStr|
  ensures |subStr| == 0 || aStr[index..index+|subStr|] == subStr
  ensures forall j :: index < j <= endPos && j + |subStr| <= |aStr| ==> |subStr| == 0 || aStr[j..j+|subStr|] != subStr
{
  if |subStr| == 0 then
    endPos  // Empty substring: return end position
  else
    var idx := endPos - |subStr|;
    while idx >= start
      decreases idx - start
      invariant idx >= start - 1
      invariant forall j :: idx < j <= endPos && j + |subStr| <= |aStr| ==> aStr[j..j+|subStr|] != subStr
    {
      if aStr[idx..idx+|subStr|] == subStr then
        return idx;
      idx := idx - 1;
    }
    // This ensures we always find the substring due to the precondition
    assert false;  // Should never reach here if precondition holds
    endPos - |subStr|
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
  /* code modified by LLM (iteration 5): Fixed while loop syntax error */
  result := [];
  var i := 0;
  while i < |a|
    decreases |a| - i
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      result[j] >= 0 &&
      start[j] <= result[j] &&
      result[j] <= endPos[j] &&
      result[j] + |sub[j]| <= |a[j]| &&
      (|sub[j]| == 0 || a[j][result[j]..result[j]+|sub[j]|] == sub[j]) &&
      (forall k :: result[j] < k <= endPos[j] && k + |sub[j]| <= |a[j]| ==> 
        |sub[j]| == 0 || a[j][k..k+|sub[j]|] != sub[j])
  {
    var idx := FindRightmostIndex(a[i], sub[i], start[i], endPos[i]);
    result := result + [idx];
    i := i + 1;
  }
}
// </vc-code>
