// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FindHelper(a: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos < |a|
  requires |sub| > 0
  requires start + |sub| <= |a|
  ensures result >= -1
  ensures result == -1 ==> (
    forall pos :: start <= pos <= endPos && pos + |sub| <= |a| ==> a[pos..pos+|sub|] != sub
  )
  ensures result >= 0 ==> (
    start <= result <= endPos &&
    result + |sub| <= |a| &&
    a[result..result+|sub|] == sub &&
    forall pos :: start <= pos < result && pos + |sub| <= |a| ==> a[pos..pos+|sub|] != sub
  )
{
  var pos := start;
  while pos <= endPos && pos + |sub| <= |a|
    invariant start <= pos <= endPos + 1
    invariant forall p :: start <= p < pos && p + |sub| <= |a| ==> a[p..p+|sub|] != sub
  {
    if a[pos..pos+|sub|] == sub then {
      return pos;
    }
    pos := pos + 1;
  }
  -1
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
  /* code modified by LLM (iteration 5): Fixed parse error in while condition */
  var resultSeq: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant |resultSeq| == i
    invariant forall j :: 0 <= j < i ==> (
      (|sub[j]| == 0 ==> resultSeq[j] == start[j]) &&
      (start[j] + |sub[j]| > |a[j]| ==> resultSeq[j] == -1) &&
      (start[j] > endPos[j] ==> resultSeq[j] == -1) &&
      (|sub[j]| > 0 && start[j] + |sub[j]| <= |a[j]| && start[j] <= endPos[j] ==> (
        (resultSeq[j] == -1 <==> 
          (forall pos :: start[j] <= pos <= endPos[j] && pos + |sub[j]| <= |a[j]| ==> a[j][pos..pos+|sub[j]|] != sub[j])) &&
        (resultSeq[j] >= 0 ==> (
          start[j] <= resultSeq[j] <= endPos[j] &&
          resultSeq[j] + |sub[j]| <= |a[j]| &&
          a[j][resultSeq[j]..resultSeq[j]+|sub[j]|] == sub[j] &&
          (forall pos :: start[j] <= pos < resultSeq[j] && pos + |sub[j]| <= |a[j]| ==> a[j][pos..pos+|sub[j]|] != sub[j])))
      ))
    )
  {
    var res := -1;
    if |sub[i]| == 0 {
      res := start[i];
    } else if start[i] + |sub[i]| > |a[i]| {
      res := -1;
    } else if start[i] > endPos[i] {
      res := -1;
    } else {
      res := FindHelper(a[i], sub[i], start[i], endPos[i]);
    }
    resultSeq := resultSeq + [res];
    i := i + 1;
  }
  result := resultSeq;
}
// </vc-code>
