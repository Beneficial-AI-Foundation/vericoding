// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): rfind_single handles bounds and empty-sub edgecases */
method rfind_single(a: string, sub: string, start: int, endPos: int) returns (res: int)
  requires 0 <= start <= endPos
  ensures (res == -1) ==> (forall j :: start <= j && j + |sub| <= endPos + 1 && j + |sub| <= |a| ==> a[j..j+|sub|] != sub)
  ensures (res >= 0) ==> start <= res && res + |sub| <= endPos + 1 && res + |sub| <= |a| && a[res..res+|sub|] == sub && (forall j :: (res < j && j + |sub| <= endPos + 1 && start <= j && j + |sub| <= |a|) ==> a[j..j+|sub|] != sub)
{
  // If sub is longer than a, it cannot occur
  if |sub| > |a| {
    res := -1;
    return;
  }
  // Compute the largest start we should consider, respecting bounds and empty-sub semantics
  var maxStart := if |sub| == 0 then (if |a| == 0 then -1 else |a| - 1) else |a| - |sub|;
  var end := if endPos < maxStart then endPos else maxStart;
  // Empty search range
  if start > end {
    res := -1;
    return;
  }
  var last := -1;
  var j := start;
  while j <= end
    invariant -1 <= last < |a|
    invariant start <= j <= end + 1
    invariant forall k :: start <= k < j && k + |sub| <= endPos + 1 && k + |sub| <= |a| ==> (a[k..k+|sub|] == sub ==> last >= k)
    decreases end - j + 1
  {
    if j + |sub| <= endPos + 1 && j + |sub| <= |a| && a[j..j+|sub|] == sub {
      last := j;
    }
    j := j + 1;
  }
  res := last;
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
/* code modified by LLM (iteration 5): iterate elements and use rfind_single per index */
{
  var arr := new int[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant arr.Length == |a|
    invariant forall k :: 0 <= k < i ==> (arr[k] == -1 || 0 <= arr[k] < |a[k]|)
    invariant forall k :: 0 <= k < i ==> (arr[k] == -1 ==> (forall j :: start[k] <= j && j + |sub[k]| <= endPos[k] + 1 && j + |sub[k]| <= |a[k]| ==> a[k][j..j+|sub[k]|] != sub[k])))
    invariant forall k :: 0 <= k < i ==> (arr[k] >= 0 ==> start[k] <= arr[k] && arr[k] + |sub[k]| <= endPos[k] + 1 && arr[k] + |sub[k]| <= |a[k]| && a[k][arr[k]..arr[k]+|sub[k]|] == sub[k] && (forall j :: arr[k] < j && j + |sub[k]| <= endPos[k] + 1 && start[k] <= j && j + |sub[k]| <= |a[k]| ==> a[k][j..j+|sub[k]|] != sub[k])))
    decreases |a| - i
  {
    arr[i] := rfind_single(a[i], sub[i], start[i], endPos[i]);
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
