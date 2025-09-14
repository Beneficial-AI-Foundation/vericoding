// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop invariant by ensuring currentLength starts at 1 and tracks subsequence properly */
    result := 0;
    if a.Length == 0 {
        return;
    }
    
    var maxLength := 1;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant maxLength >= 1
        invariant maxLength <= a.Length
    {
        var currentLength := 1;
        var j := i + 1;
        var lastElement := a[i];
        
        while j < a.Length
            invariant i < j <= a.Length
            invariant currentLength >= 1
            invariant currentLength <= j - i
        {
            if a[j] > lastElement {
                currentLength := currentLength + 1;
                lastElement := a[j];
            }
            j := j + 1;
        }
        
        maxLength := IntMax(maxLength, currentLength);
        i := i + 1;
    }
    
    result := maxLength;
}
// </vc-code>
