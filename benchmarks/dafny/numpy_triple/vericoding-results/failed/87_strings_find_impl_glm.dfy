// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }

function isSubstringFound(s: string, sub: string, pos: int): bool {
    pos + |sub| <= |s| && s[pos..pos + |sub|] == sub
}

/* helper modified by LLM (iteration 2): fixed set comprehension syntax and used Set.Min for non-empty sets */
function findSubstringInRange(s: string, sub: string, start: int, endPos: int): int {
    if |sub| == 0 then start
    else if start > endPos || start + |sub| > |s| then -1
    else
        var candidates := { p | start <= p <= endPos && p + |sub| <= |s| && isSubstringFound(s, sub, p) };
        if candidates == {} then -1
        else Set.Min(candidates)
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
  /* code modified by LLM (iteration 2): using fixed helper function in loop */
  result := new int[|a|];
  for i := 0 to |a|
    invariant |result| == |a|
    invariant forall j :: 0 <= j < i ==> result[j] == findSubstringInRange(a[j], sub[j], start[j], endPos[j])
  {
    result[i] := findSubstringInRange(a[i], sub[i], start[i], endPos[i]);
  }
}
// </vc-code>
