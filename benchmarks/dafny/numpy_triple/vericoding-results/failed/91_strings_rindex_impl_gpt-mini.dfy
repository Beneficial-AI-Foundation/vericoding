// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ensure index bounds when slicing string */
function IsMatch(a: string, sub: string, idx: int): bool {
  0 <= idx && idx + |sub| <= |a| && (|sub| == 0 || a[idx..idx+|sub|] == sub)
}

/* helper modified by LLM (iteration 5): instantiate existence of precondition match for index */
lemma MatchExistsForIndex(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>, i: int)
  requires |a| == |sub| == |start| == |endPos|
  requires 0 <= i < |a|
  requires forall k :: 0 <= k < |a| ==>
    0 <= start[k] <= endPos[k] <= |a[k]| &&
    exists j {:trigger a[k][j..j+|sub[k]|]} :: start[k] <= j && j + |sub[k]| <= |a[k]| && j <= endPos[k] && (|sub[k]| == 0 || a[k][j..j+|sub[k]|] == sub[k])
  ensures exists j :: start[i] <= j && j + |sub[i]| <= |a[i]| && j <= endPos[i] && (|sub[i]| == 0 || a[i][j..j+|sub[i]|] == sub[i])
{
  // The ensures follows by instantiating the required forall-quantifier at index i.
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
  /* code modified by LLM (iteration 5): instantiate witness via lemma and scan forward to find rightmost match */
  var n := |a|;
  var R := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==>
      R[k] >= 0 && start[k] <= R[k] && R[k] <= endPos[k] && R[k] + |sub[k]| <= |a[k]| &&
      (|sub[k]| == 0 || a[k][R[k]..R[k]+|sub[k]|] == sub[k]) &&
      (forall j {:trigger a[k][j..j+|sub[k]|]} :: R[k] < j <= endPos[k] && j + |sub[k]| <= |a[k]| ==> |sub[k]| == 0 || a[k][j..j+|sub[k]|] != sub[k])
    decreases n - i
  {
    var kidx := i;
    if |sub[kidx]| == 0 {
      R[i] := endPos[kidx];
    } else {
      var limit := if endPos[kidx] <= |a[kidx]| - |sub[kidx]| then endPos[kidx] else |a[kidx]| - |sub[kidx]|;

      // Bring the existential match for this index into scope so we can pick a witness
      MatchExistsForIndex(a, sub, start, endPos, kidx);
      var w :| start[kidx] <= w && w + |sub[kidx]| <= |a[kidx]| && w <= endPos[kidx] && (|sub[kidx]| == 0 || a[kidx][w..w+|sub[kidx]|] == sub[kidx]);
      var last := w;

      var j := w + 1;
      while j <= limit
        invariant start[kidx] <= w <= last <= j <= limit + 1
        invariant last + |sub[kidx]| <= |a[kidx]|
        invariant (|sub[kidx]| == 0 || a[kidx][last..last+|sub[kidx]|] == sub[kidx])
        decreases limit - j + 1
      {
        if a[kidx][j..j+|sub[kidx]|] == sub[kidx] {
          last := j;
        }
        j := j + 1;
      }
      R[i] := last;
    }

    i := i + 1;
  }
  result := R[..];
}

// </vc-code>
