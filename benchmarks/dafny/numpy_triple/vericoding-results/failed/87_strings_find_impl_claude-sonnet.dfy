// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper predicates to focus on core substring operations */
predicate SubstringMatch(s: string, sub: string, pos: int)
  requires 0 <= pos && pos + |sub| <= |s|
{
  s[pos..pos + |sub|] == sub
}

lemma SubstringMatchProperties(s: string, sub: string, pos: int)
  requires 0 <= pos && pos + |sub| <= |s|
  ensures SubstringMatch(s, sub, pos) <==> s[pos..pos + |sub|] == sub
{
}

lemma SearchRangeProperties(s: string, sub: string, startPos: int, endPos: int)
  requires 0 <= startPos <= endPos < |s|
  requires |sub| > 0
  ensures (forall pos :: startPos <= pos <= endPos && pos + |sub| <= |s| ==> s[pos..pos + |sub|] != sub) <=>
          (forall pos :: startPos <= pos <= endPos && pos + |sub| <= |s| ==> !SubstringMatch(s, sub, pos))
{
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
  /* code modified by LLM (iteration 5): simplified implementation with better invariant maintenance */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (
      (|sub[j]| == 0 ==> result[j] == start[j]) &&
      (start[j] + |sub[j]| > |a[j]| ==> result[j] == -1) &&
      (start[j] > endPos[j] ==> result[j] == -1) &&
      (|sub[j]| > 0 && start[j] + |sub[j]| <= |a[j]| && start[j] <= endPos[j] ==> (
        (result[j] == -1 <==> 
          (forall pos {:trigger a[j][pos..pos + |sub[j]|]} :: start[j] <= pos <= endPos[j] && pos + |sub[j]| <= |a[j]| ==> a[j][pos..pos + |sub[j]|] != sub[j])) &&
        (result[j] >= 0 ==> (
          start[j] <= result[j] <= endPos[j] &&
          result[j] + |sub[j]| <= |a[j]| &&
          a[j][result[j]..result[j] + |sub[j]|] == sub[j] &&
          (forall pos {:trigger a[j][pos..pos + |sub[j]|]} :: start[j] <= pos < result[j] && pos + |sub[j]| <= |a[j]| ==> a[j][pos..pos + |sub[j]|] != sub[j])))
      ))
    )
  {
    var foundIndex := -1;
    
    if |sub[i]| == 0 {
      foundIndex := start[i];
    } else if start[i] + |sub[i]| > |a[i]| || start[i] > endPos[i] {
      foundIndex := -1;
    } else {
      var pos := start[i];
      while pos <= endPos[i] && pos + |sub[i]| <= |a[i]| && foundIndex == -1
        invariant start[i] <= pos <= endPos[i] + 1
        invariant foundIndex == -1
        invariant forall p :: start[i] <= p < pos && p + |sub[i]| <= |a[i]| ==> a[i][p..p + |sub[i]|] != sub[i]
        decreases endPos[i] + 1 - pos
      {
        if a[i][pos..pos + |sub[i]|] == sub[i] {
          foundIndex := pos;
        } else {
          pos := pos + 1;
        }
      }
    }
    
    result := result + [foundIndex];
    i := i + 1;
  }
}
// </vc-code>
