// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function rightmostSearch(s: string, sub: string, startAt: int, endBefore: int): int
  requires 0 <= startAt <= endBefore <= |s|
  requires |sub| > 0
  ensures pos == -1 || (startAt <= pos <= endBefore - |sub|)
  ensures pos == -1 ==> forall j :: startAt <= j <= endBefore - |sub| ==> s[j..j+|sub|] != sub
  ensures pos >= 0 ==> s[pos..pos+|sub|] == sub && forall j :: pos < j <= endBefore - |sub| ==> s[j..j+|sub|] != sub
{
  /* helper modified by LLM (iteration 5): Fixed while condition syntax */
  var pos: int := -1;
  var j: int := endBefore - |sub|;
  while j >= startAt
    invariant startAt - 1 <= j <= endBefore - |sub|
    invariant forall k :: j < k <= endBefore - |sub| ==> s[k..k+|sub|] != sub
    decreases j + 1
  {
    if s[j..j+|sub|] == sub {
      pos := j;
      break;
    }
    j := j - 1;
  }
  pos
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
  /* code modified by LLM (iteration 5): Fixed compilation error in helper call */
  result := [];
  var i: int := 0;
  while i < |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
      result[k] == -1 || (0 <= result[k] < |a[k]|) &&
      (result[k] == -1 ==> 
        forall j :: start[k] <= j && j + |sub[k]| <= endPos[k] + 1 && j + |sub[k]| <= |a[k]| ==> 
          a[k][j..j+|sub[k]|] != sub[k]) &&
      (result[k] >= 0 ==> 
        start[k] <= result[k] && 
        result[k] + |sub[k]| <= endPos[k] + 1 &&
        result[k] + |sub[k]| <= |a[k]| &&
        a[k][result[k]..result[k]+|sub[k]|] == sub[k] &&
        forall j :: result[k] < j && j + |sub[k]| <= endPos[k] + 1 && 
                 start[k] <= j && j + |sub[k]| <= |a[k]| ==> 
          a[k][j..j+|sub[k]|] != sub[k])
  {
    if |sub[i]| == 0 {
      result := result + [0];
    } else if |sub[i]| > |a[i]| || endPos[i] - start[i] + 1 < |sub[i]| {
      result := result + [-1];
    } else {
      var pos: int := rightmostSearch(a[i], sub[i], start[i], endPos[i] + 1);
      result := result + [pos];
    }
    i := i + 1;
  }
}
// </vc-code>
