// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
}

method RFindSingle(s: string, p: string, st: int, en: int) returns (res: int)
  requires 0 <= st <= en
  ensures (res == -1 || (0 <= res < |s|)) &&
    (res == -1 ==> 
      (forall j {:trigger s[j..j+|p|]} :: st <= j && j + |p| <= en + 1 && j + |p| <= |s| ==>
        s[j..j+|p|] != p)) &&
    (res >= 0 ==> 
      st <= res && 
      res + |p| <= en + 1 &&
      res + |p| <= |s| &&
      s[res..res+|p|] == p &&
      (forall j {:trigger s[j..j+|p|]} :: (res < j && j + |p| <= en + 1 && 
                   st <= j && j + |p| <= |s|) ==> 
        s[j..j+|p|] != p))
{
  if |p| <= |s| {
    var high := min(|s| - |p|, en + 1 - |p|);
    var j := high;
    while j >= st
      invariant st <= j + 1
      invariant forall k :: j < k <= high ==> s[k..k+|p|] != p
    {
      if s[j..j+|p|] == p {
        res := j;
        return;
      }
      j := j - 1;
    }
  }
  res := -1;
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
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant |a| == |sub| == |start| == |endPos|
    invariant forall k :: 0 <= k < |a| ==> 0 <= start[k] <= endPos[k]
    invariant forall k :: 0 <= k < i ==> 
      (result[k] == -1 || (0 <= result[k] < |a[k]|)) &&
      (result[k] == -1 ==> 
        (forall j {:trigger a[k][j..j+|sub[k]|]} :: start[k] <= j && j + |sub[k]| <= endPos[k] + 1 && j + |sub[k]| <= |a[k]| ==>
          a[k][j..j+|sub[k]|] != sub[k])) &&
      (result[k] >= 0 ==> 
        start[k] <= result[k] && 
        result[k] + |sub[k]| <= endPos[k] + 1 && 
        result[k] + |sub[k]| <= |a[k]| &&
        a[k][result[k]..result[k]+|sub[k]|] == sub[k] &&
        (forall j' {:trigger a[k][j'..j'+|sub[k]|]} :: (result[k] < j' && j' + |sub[k]| <= endPos[k] + 1 && 
                     start[k] <= j' && j' + |sub[k]| <= |a[k]|) ==> 
          a[k][j'..j'+|sub[k]|] != sub[k]))
  {
    var r := RFindSingle(a[i], sub[i], start[i], endPos[i]);
    result := result + [r];
    i := i + 1;
  }
}
// </vc-code>
