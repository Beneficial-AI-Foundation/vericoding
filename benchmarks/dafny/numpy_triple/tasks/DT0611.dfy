// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
