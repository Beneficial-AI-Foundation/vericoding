// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to derive existence up to j from global existence and no matches after j */
lemma ExistsUpToJ(a: string, sub: string, start: int, j: int, endp: int)
  requires 0 <= start <= j <= endp <= |a|
  requires exists k {:trigger a[k..k+|sub|]} :: start <= k <= endp && k + |sub| <= |a| && (|sub| == 0 || a[k..k+|sub|] == sub)
  requires forall m {:trigger a[m..m+|sub|]} :: j < m <= endp && m + |sub| <= |a| ==> (|sub| == 0 || a[m..m+|sub|] != sub)
  ensures exists k {:trigger a[k..k+|sub|]} :: start <= k <= j && k + |sub| <= |a| && (|sub| == 0 || a[k..k+|sub|] == sub)
{
  var k: int :| start <= k <= endp && k + |sub| <= |a| && (|sub| == 0 || a[k..k+|sub|] == sub);
  if k <= j {
  } else {
    assert j < k <= endp && k + |sub| <= |a|;
    assert (|sub| == 0 || a[k..k+|sub|] != sub);
    assert false;
  }
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
  /* code modified by LLM (iteration 5): implement right-to-left scan per element, maintaining no-matches-after-j invariant and using existence from preconditions */
  var n := |a|;
  var res: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==>
      res[k] >= 0 &&
      start[k] <= res[k] <= endPos[k] &&
      res[k] + |sub[k]| <= |a[k]| &&
      (|sub[k]| == 0 || a[k][res[k]..res[k] + |sub[k]|] == sub[k]) &&
      (forall j {:trigger a[k][j..j+|sub[k]|]} :: res[k] < j <= endPos[k] && j + |sub[k]| <= |a[k]| ==> (|sub[k]| == 0 || a[k][j..j + |sub[k]|] != sub[k]))
    decreases n - i
  {
    var j := endPos[i];
    while true
      invariant start[i] <= j <= endPos[i]
      invariant exists t {:trigger a[i][t..t+|sub[i]|]} :: start[i] <= t <= endPos[i] && t + |sub[i]| <= |a[i]| && (|sub[i]| == 0 || a[i][t..t+|sub[i]|] == sub[i])
      invariant forall m {:trigger a[i][m..m+|sub[i]|]} :: j < m <= endPos[i] && m + |sub[i]| <= |a[i]| ==> (|sub[i]| == 0 || a[i][m..m+|sub[i]|] != sub[i])
      decreases j - start[i] + 1
    {
      if j + |sub[i]| <= |a[i]| && (|sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i]) {
        break;
      } else {
        ghost var w: int :| start[i] <= w <= endPos[i] && w + |sub[i]| <= |a[i]| && (|sub[i]| == 0 || a[i][w..w+|sub[i]|] == sub[i]);
        if j < w {
          assert !(j < w); // contradiction with the no-matches-after-j invariant
        }
        assert w <= j;
        if w == j {
          if j + |sub[i]| > |a[i]| {
            assert false; // w cannot be out of bounds by construction
          } else {
            assert (|sub[i]| == 0 || a[i][j..j+|sub[i]|] != sub[i]);
            assert (|sub[i]| == 0 || a[i][w..w+|sub[i]|] == sub[i]);
            assert false;
          }
        }
        assert w < j;
        assert j > start[i]; // since start <= w < j
        j := j - 1;
      }
    }
    res := res + [j];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
