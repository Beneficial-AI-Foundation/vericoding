// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate matches(s: string, sub: string, pos: nat)
  requires pos + |sub| <= |s|
{
  |sub| == 0 || s[pos..pos+|sub|] == sub
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
/* code modified by LLM (iteration 5): fixed the loop invariant by changing the while condition to while j >= min_p and using a break when matches is true, ensuring j remains within min_p to max_p */
{
  var positions := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |positions| == i
  {
    var min_p := start[i];
    var max_val := |a[i]| - |sub[i]|;
    var max_p := if max_val < endPos[i] then max_val else endPos[i];
    var j := max_p;
    while j >= min_p
      invariant min_p <= j <= max_p
      decreases j
    {
      if matches(a[i], sub[i], j) {
        break;
      }
      j := j - 1;
    }
    positions := positions + [j];
    i := i + 1;
  }
  result := positions;
}
// </vc-code>
