// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix predicate bounds check */
predicate SubstringMatch(s: string, sub: string, pos: int)
{
  0 <= pos && pos + |sub| <= |s| && (|sub| == 0 || s[pos..pos+|sub|] == sub)
}

/* helper modified by LLM (iteration 5): add lemma to establish initial rightmost index */
lemma InitialRightmostExists(s: string, sub: string, start: int, endPos: int)
  requires 0 <= start <= endPos <= |s|
  requires exists j :: start <= j <= endPos && j + |sub| <= |s| && SubstringMatch(s, sub, j)
  ensures exists j :: start <= j <= endPos && j + |sub| <= |s| && SubstringMatch(s, sub, j) && start <= j
{
  // Proof follows from precondition
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
  /* code modified by LLM (iteration 5): fix loop entry invariants and postcondition */
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
      (forall j :: result[k] < j <= endPos[k] && j + |sub[k]| <= |a[k]| ==>
        |sub[k]| == 0 || a[k][j..j+|sub[k]|] != sub[k])
  {
    // Find an initial valid position from the precondition
    var rightmostIndex := start[i];
    while rightmostIndex <= endPos[i] && (rightmostIndex + |sub[i]| > |a[i]| || (|sub[i]| > 0 && a[i][rightmostIndex..rightmostIndex+|sub[i]|] != sub[i]))
      invariant start[i] <= rightmostIndex <= endPos[i] + 1
      invariant rightmostIndex > endPos[i] || rightmostIndex + |sub[i]| > |a[i]| || 
        exists j :: start[i] <= j <= endPos[i] && j + |sub[i]| <= |a[i]| && (|sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i])
    {
      rightmostIndex := rightmostIndex + 1;
    }
    
    // Search for the rightmost occurrence starting from rightmostIndex
    var j := rightmostIndex + 1;
    while j <= endPos[i] && j + |sub[i]| <= |a[i]|
      invariant rightmostIndex + 1 <= j <= endPos[i] + 1
      invariant start[i] <= rightmostIndex <= endPos[i]
      invariant rightmostIndex + |sub[i]| <= |a[i]|
      invariant |sub[i]| == 0 || a[i][rightmostIndex..rightmostIndex+|sub[i]|] == sub[i]
      invariant forall k :: rightmostIndex < k < j && k <= endPos[i] && k + |sub[i]| <= |a[i]| ==>
        |sub[i]| == 0 || a[i][k..k+|sub[i]|] != sub[i]
    {
      if |sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i] {
        rightmostIndex := j;
      }
      j := j + 1;
    }
    result := result + [rightmostIndex];
    i := i + 1;
  }
}
// </vc-code>
