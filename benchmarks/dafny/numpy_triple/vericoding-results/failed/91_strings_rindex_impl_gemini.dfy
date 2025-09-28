// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used a nested ghost method to obtain a witness, fixing compilation error. */
lemma WitnessIsSmaller(s: string, sub: string, start: int, i: int)
  requires |sub| > 0
  requires 0 <= start <= i
  requires i + |sub| > |s| || s[i..i+|sub|] != sub
  requires exists j {:trigger s[j..j+|sub|]} :: start <= j <= i && j + |sub| <= |s| && s[j..j+|sub|] == sub
  ensures exists j {:trigger s[j..j+|sub|]} :: start <= j < i && j + |sub| <= |s| && s[j..j+|sub|] == sub
{
  ghost method FindWitness() returns (j: int)
    ensures start <= j <= i && j + |sub| <= |s| && s[j..j+|sub|] == sub
  {
    j :| start <= j <= i && j + |sub| <= |s| && s[j..j+|sub|] == sub;
  }
  var j_witness := FindWitness();
  if j_witness == i {
    assert i + |sub| <= |s| && s[i..i+|sub|] == sub;
    assert false;
  }
}

method ComputeRightmostIndex(s: string, sub: string, start: int, endPos: int) returns (result: int)
  requires 0 <= start <= endPos <= |s|
  requires exists j {:trigger s[j..j+|sub|]} :: start <= j && j <= endPos && j + |sub| <= |s| && (|sub| == 0 || s[j..j+|sub|] == sub)

  ensures start <= result <= endPos
  ensures result + |sub| <= |s|
  ensures |sub| == 0 || s[result..result+|sub|] == sub
  ensures forall k {:trigger s[k..k+|sub|]} :: result < k && k <= endPos && k + |sub| <= |s| ==> (|sub| == 0 || s[k..k+|sub|] != sub)
{
  if |sub| == 0 {
    result := endPos;
    return;
  }

  var i := endPos;
  while start <= i
    decreases i
    invariant start <= i <= endPos
    invariant |sub| > 0
    invariant forall k {:trigger s[k..k+|sub|]} :: i < k && k <= endPos && k + |sub| <= |s| ==> s[k..k+|sub|] != sub
    invariant exists j {:trigger s[j..j+|sub|]} :: start <= j <= i && j + |sub| <= |s| && s[j..j+|sub|] == sub
  {
    if i + |sub| <= |s| && s[i..i+|sub|] == sub {
      result := i;
      return;
    }

    WitnessIsSmaller(s, sub, start, i);
    i := i - 1;
  }
  assert false; // Should be an unreachable code path
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
  /* code modified by LLM (iteration 5): Added forall invariant to prove helper precondition. */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant |a| == |sub| == |start| == |endPos|
    invariant forall k :: 0 <= k < |a| ==>
      0 <= start[k] <= endPos[k] <= |a[k]| &&
      (exists j {:trigger a[k][j..j+|sub[k]|]} :: start[k] <= j && 
                  j + |sub[k]| <= |a[k]| &&
                  j <= endPos[k] &&
                  (|sub[k]| == 0 || a[k][j..j+|sub[k]|] == sub[k]))
    invariant forall k :: 0 <= k < i ==>
      result[k] >= 0 &&
      start[k] <= result[k] <= endPos[k] &&
      result[k] + |sub[k]| <= |a[k]| &&
      (|sub[k]| == 0 || a[k][result[k]..result[k]+|sub[k]|] == sub[k]) &&
      (forall j {:trigger a[k][j..j+|sub[k]|]} :: result[k] < j <= endPos[k] && j + |sub[k]| <= |a[k]| ==>
        |sub[k]| == 0 || a[k][j..j+|sub[k]|] != sub[k])
  {
    var r_i := ComputeRightmostIndex(a[i], sub[i], start[i], endPos[i]);
    result := result + [r_i];
    i := i + 1;
  }
}
// </vc-code>
