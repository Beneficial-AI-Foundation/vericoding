// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected loop invariant to match postconditions */
method FindFirst(a: string, sub: string, start: int, endPos: int) returns (res: int)
  requires 0 <= start <= endPos < |a|
  ensures |sub| == 0 ==> res == start
  ensures start + |sub| > |a| ==> res == -1
  ensures start > endPos ==> res == -1
  ensures |sub| > 0 && start + |sub| <= |a| && start <= endPos ==> (
    (res == -1 <==> (forall pos {:trigger a[pos..pos + |sub|]} :: start <= pos <= endPos && pos + |sub| <= |a| ==> a[pos..pos + |sub|] != sub)) &&
    (res >= 0 ==> start <= res <= endPos && res + |sub| <= |a| && a[res..res + |sub|] == sub &&
      (forall pos {:trigger a[pos..pos + |sub|]} :: start <= pos < res && pos + |sub| <= |a| ==> a[pos..pos + |sub|] != sub))
  )
{
  if |sub| == 0 {
    res := start;
    return;
  }
  if start + |sub| > |a| {
    res := -1;
    return;
  }
  var pos := start;
  while pos <= endPos
    invariant start <= pos <= endPos + 1
    invariant forall p {:trigger a[p..p + |sub|]} :: start <= p < pos && p + |sub| <= |a| ==> a[p..p + |sub|] != sub
    decreases endPos - pos + 1
  {
    if pos + |sub| <= |a| && a[pos..pos + |sub|] == sub {
      res := pos;
      return;
    }
    pos := pos + 1;
  }
  res := -1;
}

// </vc-helpers>

// <vc-spec>
method Find(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) 
    returns (result: seq<int>)
    // Input arrays must have the same length
    requires |a| == |sub| == |start| == |endPos|
    // Start and end positions must be valid for each string
    requires forall i :: 0 <= i < |a| ==> 
        0 <= start[i] <= endPos[i] < |a[i]|
    
    // Output has same length as inputs
    ensures |result| == |a|
    
    // Main specification for each element
    ensures forall i :: 0 <= i < |result| ==> (
        // Special cases (these take precedence)
        (|sub[i]| == 0 ==> result[i] == start[i]) &&
        (start[i] + |sub[i]| > |a[i]| ==> result[i] == -1) &&
        (start[i] > endPos[i] ==> result[i] == -1) &&
        
        // General cases only apply when special cases don't
        (|sub[i]| > 0 && start[i] + |sub[i]| <= |a[i]| && start[i] <= endPos[i] ==> (
            // Case 1: substring not found (returns -1)
            (result[i] == -1 <==> 
                (forall pos {:trigger a[i][pos..pos + |sub[i]|]} :: start[i] <= pos <= endPos[i] && pos + |sub[i]| <= |a[i]| ==>
                    a[i][pos..pos + |sub[i]|] != sub[i])) &&
            
            // Case 2: substring found (returns non-negative index)
            (result[i] >= 0 ==> (
                // Result is within valid range
                start[i] <= result[i] <= endPos[i] &&
                result[i] + |sub[i]| <= |a[i]| &&
                // Substring actually found at this position
                a[i][result[i]..result[i] + |sub[i]|] == sub[i] &&
                // This is the LOWEST index where substring is found (minimality)
                (forall pos {:trigger a[i][pos..pos + |sub[i]|]} :: start[i] <= pos < result[i] && pos + |sub[i]| <= |a[i]| ==>
                    a[i][pos..pos + |sub[i]|] != sub[i])))
        ))
    )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate and call FindFirst per element with corrected invariants */
{
  var out := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |out| == i
    invariant forall k {:trigger a[k][0..0]} :: 0 <= k < |out| ==> (
      (|sub[k]| == 0 ==> out[k] == start[k]) &&
      (start[k] + |sub[k]| > |a[k]| ==> out[k] == -1) &&
      (start[k] > endPos[k] ==> out[k] == -1) &&
      (|sub[k]| > 0 && start[k] + |sub[k]| <= |a[k]| && start[k] <= endPos[k] ==>
        ((out[k] == -1 <==> (forall pos {:trigger a[k][pos..pos + |sub[k]|]} :: start[k] <= pos <= endPos[k] && pos + |sub[k]| <= |a[k]| ==> a[k][pos..pos + |sub[k]|] != sub[k]))) &&
        (out[k] >= 0 ==> (
            start[k] <= out[k] <= endPos[k] &&
            out[k] + |sub[k]| <= |a[k]| &&
            a[k][out[k]..out[k] + |sub[k]|] == sub[k] &&
            (forall pos {:trigger a[k][pos..pos + |sub[k]|]} :: start[k] <= pos < out[k] && pos + |sub[k]| <= |a[k]| ==> a[k][pos..pos + |sub[k]|] != sub[k])
        ))
      )
  {
    var r := FindFirst(a[i], sub[i], start[i], endPos[i]);
    out := out + [r];
    i := i + 1;
  }
  result := out;
}

// </vc-code>
