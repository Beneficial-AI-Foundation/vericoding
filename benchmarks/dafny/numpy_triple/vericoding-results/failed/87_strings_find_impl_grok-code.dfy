// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add parentheses to fix indentation warnings */
method FindSub(s: string, sub: string, low: int, high: int) returns (pos: int)
  requires 0 <= low <= high + 1 <= |s|
  ensures (|sub| == 0 ==> pos == low) &&
          (low + |sub| > |s| ==> pos == -1) &&
          (low > high ==> pos == -1) &&
          (|sub| > 0 && low + |sub| <= |s| && low <= high ==> (
            (pos == -1 <==> forall p {:trigger s[p..p + |sub|]} :: low <= p <= high && p + |sub| <= |s| ==> s[p..p + |sub|] != sub) &&
            (pos >= 0 ==> (low <= pos <= high && pos + |sub| <= |s| && s[pos..pos + |sub|] == sub &&
             forall p {:trigger s[p..p + |sub|]} :: low <= p < pos && p + |sub| <= |s| ==> s[p..p + |sub|] != sub))
          ))
{
  if |sub| == 0 {
    pos := low;
  } else if low > high {
    pos := -1;
  } else if low + |sub| > |s| {
    pos := -1;
  } else {
    var j := low;
    while j <= high && j + |sub| <= |s|
      invariant low <= j <= high + 1
      invariant forall p {:trigger s[p..p + |sub|]} :: low <= p < j && p + |sub| <= |s| ==> s[p..p + |sub|] != sub
    {
      if s[j..j + |sub|] == sub {
        pos := j;
        return;
      }
      j := j + 1;
    }
    pos := -1;
  }
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
{
  /* code modified by LLM (iteration 5): fix for loop syntax to proper Dafny */
  var positions: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant |positions| == i
  {
    if |sub[i]| == 0 {
      positions := positions + [start[i]];
    } else if start[i] > endPos[i] {
      positions := positions + [-1];
    } else if start[i] + |sub[i]| > |a[i]| {
      positions := positions + [-1];
    } else {
      var pos := FindSub(a[i], sub[i], start[i], endPos[i]);
      positions := positions + [pos];
    }
    i := i + 1;
  }
  result := positions;
}
// </vc-code>
