// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added requires and triggers */
method FindOne(a: string, sub: string, start: int, endPos: int) returns (result: int)
    requires 0 <= start
    ensures (|sub| == 0 ==> result == start)
    ensures (start + |sub| > |a| ==> result == -1)
    ensures (start > endPos ==> result == -1)
    ensures |sub| > 0 && start + |sub| <= |a| && start <= endPos ==> (
        (result == -1 <==> 
            (forall pos {:trigger a[pos..pos + |sub|]} :: start <= pos <= endPos && pos + |sub| <= |a| ==>
                a[pos..pos + |sub|] != sub)) &&
        (result >= 0 ==> (
            start <= result <= endPos &&
            result + |sub| <= |a| &&
            a[result..result + |sub|] == sub &&
            (forall pos {:trigger a[pos..pos + |sub|]} :: start <= pos < result && pos + |sub| <= |a| ==>
                a[pos..pos + |sub|] != sub)))
    )
{
    if |sub| == 0 {
        result := start;
        return;
    }
    if start > endPos || start + |sub| > |a| {
        result := -1;
        return;
    }

    var pos := start;
    while pos <= endPos && pos + |sub| <= |a|
        invariant start <= pos
        invariant forall p {:trigger a[p..p + |sub|]} :: start <= p < pos && p + |sub| <= |a| ==> a[p..p + |sub|] != sub
        decreases endPos - pos
    {
        if a[pos..pos + |sub|] == sub {
            result := pos;
            return;
        }
        pos := pos + 1;
    }
    result := -1;
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
  /* code modified by LLM (iteration 3): no logical change, helper fix is key */
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
                    a[j][pos..pos + |sub[j]|] != sub[j])))
        ))
    )
    decreases |a| - i
  {
    var res_i := FindOne(a[i], sub[i], start[i], endPos[i]);
    result := result + [res_i];
    i := i + 1;
  }
}
// </vc-code>
