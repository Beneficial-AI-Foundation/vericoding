// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function method Min(a: int, b: int): int {
  if a < b then a else b
}

predicate method ValidStart(s: string, t: string, st: int, e: int, j: int)
{
  st <= j && j + |t| <= e + 1 && j + |t| <= |s|
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
  var n := |a|;
  var res := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var s := a[i];
    var t := sub[i];
    var st := start[i];
    var e := endPos[i];
    var ls := |s|;
    var lt := |t|;
    var ub := e + 1 - lt;
    if ls - lt < ub {
      ub := ls - lt;
    }
    var j := ub;
    var found := false;
    var best := -1;
    while j >= st && !found
      invariant st <= e
      invariant 0 <= st
      invariant j <= ub
      invariant -1 <= best
      invariant (!found ==> best == -1)
      invariant (forall k {:trigger s[k..k+lt]} :: (j < k && k <= ub) ==> s[k..k+lt] != t)
      decreases j - st + 1
    {
      if s[j..j+lt] == t {
        found := true;
        best := j;
      } else {
        j := j - 1;
      }
    }
    if found {
      res[i] := best;
    } else {
      res[i] := -1;
    }
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>
