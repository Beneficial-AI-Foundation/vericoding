// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  /* code modified by LLM (iteration 5): fix loop invariants and quantifier triggers */
  var temp := seq(|a|, i => 0);
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |temp| == |a|
    invariant forall j :: 0 <= j < i ==>
      temp[j] >= 0 &&
      start[j] <= temp[j] &&
      temp[j] <= endPos[j] &&
      temp[j] + |sub[j]| <= |a[j]| &&
      (|sub[j]| == 0 || a[j][temp[j]..temp[j]+|sub[j]|] == sub[j]) &&
      (forall k {:trigger a[j][k..k+|sub[j]|]} :: temp[j] < k <= endPos[j] && k + |sub[j]| <= |a[j]| ==>
        |sub[j]| == 0 || a[j][k..k+|sub[j]|] != sub[j])
  {
    var idx := endPos[i];
    while idx >= start[i]
      invariant start[i] <= idx <= endPos[i] + 1
      invariant forall j {:trigger a[i][j..j+|sub[i]|]} :: idx < j <= endPos[i] && j + |sub[i]| <= |a[i]| ==>
        |sub[i]| == 0 || a[i][j..j+|sub[i]|] != sub[i]
    {
      if idx + |sub[i]| <= |a[i]| && (|sub[i]| == 0 || a[i][idx..idx+|sub[i]|] == sub[i]) {
        temp := temp[i := idx];
        break;
      }
      idx := idx - 1;
    }
    if idx < start[i] {
      temp := temp[i := start[i]];
    }
  }
  result := temp;
}
// </vc-code>
