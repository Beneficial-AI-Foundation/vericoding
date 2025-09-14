// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(numbers: array<int>) returns (result: nat)
    ensures result <= numbers.Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop invariant by ensuring currentLength is properly bounded */
    result := 0;
    if numbers.Length == 0 {
        return;
    }
    
    var maxLength := 1;
    var i := 0;
    
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant maxLength >= 1
        invariant maxLength <= numbers.Length
    {
        var currentLength := 1;
        var j := i + 1;
        
        while j < numbers.Length
            invariant i < j <= numbers.Length
            invariant currentLength >= 1
            invariant currentLength <= j - i
        {
            if numbers[j-1] < numbers[j] {
                currentLength := currentLength + 1;
            } else {
                break;
            }
            j := j + 1;
        }
        
        if currentLength > maxLength {
            maxLength := currentLength;
        }
        
        i := i + 1;
    }
    
    result := maxLength;
}
// </vc-code>
