// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed precondition checks and postcondition establishment in helper functions */
function FindSubstring(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos < |s|
  requires start + |sub| <= |s|
  requires |sub| > 0
  requires start <= endPos
  ensures FindSubstring(s, sub, start, endPos) == -1 || (start <= FindSubstring(s, sub, start, endPos) <= endPos && FindSubstring(s, sub, start, endPos) + |sub| <= |s|)
  ensures FindSubstring(s, sub, start, endPos) >= 0 ==> s[FindSubstring(s, sub, start, endPos)..FindSubstring(s, sub, start, endPos) + |sub|] == sub
  ensures FindSubstring(s, sub, start, endPos) >= 0 ==> forall pos {:trigger s[pos..pos + |sub|]} :: start <= pos < FindSubstring(s, sub, start, endPos) && pos + |sub| <= |s| ==> s[pos..pos + |sub|] != sub
  ensures FindSubstring(s, sub, start, endPos) == -1 ==> forall pos {:trigger s[pos..pos + |sub|]} :: start <= pos <= endPos && pos + |sub| <= |s| ==> s[pos..pos + |sub|] != sub
{
  FindSubstringHelper(s, sub, start, endPos)
}

function FindSubstringHelper(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos < |s|
  requires start + |sub| <= |s|
  requires |sub| > 0
  decreases endPos - start + 1
  ensures FindSubstringHelper(s, sub, start, endPos) == -1 || (start <= FindSubstringHelper(s, sub, start, endPos) <= endPos && FindSubstringHelper(s, sub, start, endPos) + |sub| <= |s|)
  ensures FindSubstringHelper(s, sub, start, endPos) >= 0 ==> s[FindSubstringHelper(s, sub, start, endPos)..FindSubstringHelper(s, sub, start, endPos) + |sub|] == sub
  ensures FindSubstringHelper(s, sub, start, endPos) >= 0 ==> forall pos {:trigger s[pos..pos + |sub|]} :: start <= pos < FindSubstringHelper(s, sub, start, endPos) && pos + |sub| <= |s| ==> s[pos..pos + |sub|] != sub
  ensures FindSubstringHelper(s, sub, start, endPos) == -1 ==> forall pos {:trigger s[pos..pos + |sub|]} :: start <= pos <= endPos && pos + |sub| <= |s| ==> s[pos..pos + |sub|] != sub
{
  if s[start..start + |sub|] == sub then
    start
  else if start == endPos || start + 1 + |sub| > |s| then
    -1
  else
    FindSubstringHelper(s, sub, start + 1, endPos)
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
  /* code modified by LLM (iteration 5): Added explicit triggers to loop invariants to match helper function postconditions */
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
          (forall pos {:trigger a[j][pos..pos + |sub[j]|]} :: start[j] <= pos <= endPos[j] && pos + |sub[j]| <= |a[j]| ==>
            a[j][pos..pos + |sub[j]|] != sub[j])) &&
        (result[j] >= 0 ==> (
          start[j] <= result[j] <= endPos[j] &&
          result[j] + |sub[j]| <= |a[j]| &&
          a[j][result[j]..result[j] + |sub[j]|] == sub[j] &&
          (forall pos {:trigger a[j][pos..pos + |sub[j]|]} :: start[j] <= pos < result[j] && pos + |sub[j]| <= |a[j]| ==>
            a[j][pos..pos + |sub[j]|] != sub[j]))))))
  {
    var idx: int;
    
    if |sub[i]| == 0 {
      idx := start[i];
    } else if start[i] + |sub[i]| > |a[i]| {
      idx := -1;
    } else if start[i] > endPos[i] {
      idx := -1;
    } else {
      idx := FindSubstring(a[i], sub[i], start[i], endPos[i]);
    }
    
    result := result + [idx];
    i := i + 1;
  }
}
// </vc-code>
