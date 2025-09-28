// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `found` variable was being used incorrectly. The `res` variable correctly tracks the lowest index if found, and remains -1 otherwise. Removed 'found' and simplified the loop conditions and body to solely rely on `res` for finding and tracking the index. */
function FindInString(s: string, sub: string, start: int, endPos: int): int
ensures (start + |sub| > |s| ==> FindInString(s, sub, start, endPos) == -1)
ensures (|sub| == 0 ==> FindInString(s, sub, start, endPos) == start)
ensures (start > endPos ==> FindInString(s, sub, start, endPos) == -1)
ensures (FindInString(s, sub, start, endPos) >= 0 ==> 
    start <= FindInString(s, sub, start, endPos) <= endPos &&
    FindInString(s, sub, start, endPos) + |sub| <= |s| &&
    s[FindInString(s, sub, start, endPos)..FindInString(s, sub, start, endPos) + |sub|] == sub &&
    (forall k :: start <= k < FindInString(s, sub, start, endPos) && k + |sub| <= |s| ==> s[k..k + |sub|] != sub))
ensures (FindInString(s, sub, start, endPos) == -1 ==> 
    (forall k :: start <= k <= endPos && k + |sub| <= |s| ==> s[k..k + |sub|] != sub))
{
  if |sub| == 0 then start
  else if start + |sub| > |s| || start > endPos then -1
  else 
    var i := start;
    var res := -1;
    while i <= endPos && res == -1
      invariant start <= i <= endPos + 1
      invariant res == -1 || (start <= res < i && res + |sub| <= |s| && s[res..res + |sub|] == sub && (forall k :: start <= k < res && k + |sub| <= |s| ==> s[k..k + |sub|] != sub))
      invariant (forall k :: start <= k < i && k + |sub| <= |s| ==> s[k..k + |sub|] != sub) || (res != -1 && res < i && res + |sub| <= |s| && s[res..res + |sub|] == sub)
    {
      if i + |sub| <= |s| && s[i..i + |sub|] == sub then
        res := i;
      i := i + 1;
    }
    res
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
/* code modified by LLM (iteration 5): The previous changes to the FindInString helper function should now enable this code to pass verification. No changes were made to this section in this turn. */
{
  var result_array: seq<int> := new int[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result_array| == |a|
    invariant forall k :: 0 <= k < i ==> (
        (|sub[k]| == 0 ==> result_array[k] == start[k]) &&
        (start[k] + |sub[k]| > |a[k]| ==> result_array[k] == -1) &&
        (start[k] > endPos[k] ==> result_array[k] == -1) &&
        (|sub[k]| > 0 && start[k] + |sub[k]| <= |a[k]| && start[k] <= endPos[k] ==> (
            (result_array[k] == -1 <==> 
                (forall pos :: start[k] <= pos <= endPos[k] && pos + |sub[k]| <= |a[k]| ==> a[k][pos..pos + |sub[k]|] != sub[k]))) &&
            (result_array[k] >= 0 ==> (
                start[k] <= result_array[k] <= endPos[k] &&
                result_array[k] + |sub[k]| <= |a[k]| &&
                a[k][result_array[k]..result_array[k] + |sub[k]|] == sub[k] &&
                (forall pos :: start[k] <= pos < result_array[k] && pos + |sub[k]| <= |a[k]| ==> a[k][pos..pos + |sub[k]|] != sub[k])))))
  {
    result_array[i] := FindInString(a[i], sub[i], start[i], endPos[i]);
    i := i + 1;
  }
  return result_array;
}
// </vc-code>
