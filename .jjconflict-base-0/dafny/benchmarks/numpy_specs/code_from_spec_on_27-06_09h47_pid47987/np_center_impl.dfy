//IMPL center
// Return a copy of a with its elements centered in a string of length width.
method center (input: array<string>, width:nat) returns (res: array<string>)
    requires forall i :: 0 <= i < input.Length ==> |input[i]| >= 1;
    ensures res.Length == input.Length 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| > width then |res[i]| == |input[i]| else |res[i]| == width 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| < width then res[i][(width - |input[i]|+1)/2..(width - |input[i]|+1)/2 + |input[i]|] == input[i] else true;
{
    /* code modified by LLM (iteration 1): initialize result array */
    res := new string[input.Length];
    
    /* code modified by LLM (iteration 1): fixed loop invariants and bounds checking */
    for i := 0 to input.Length
        invariant forall k :: 0 <= k < i ==> if |input[k]| > width then |res[k]| == |input[k]| else |res[k]| == width
        invariant forall k :: 0 <= k < i ==> if |input[k]| < width then res[k][(width - |input[k]|+1)/2..(width - |input[k]|+1)/2 + |input[k]|] == input[k] else true
    {
        /* code modified by LLM (iteration 1): handle case where input length >= width */
        if |input[i]| >= width {
            res[i] := input[i];
        } else {
            /* code modified by LLM (iteration 1): center the string with proper padding calculation */
            var padding_total := width - |input[i]|;
            var left_padding := (padding_total + 1) / 2;
            var right_padding := padding_total - left_padding;
            
            var spaces_left := seq(left_padding, _ => ' ');
            var spaces_right := seq(right_padding, _ => ' ');
            
            res[i] := spaces_left + input[i] + spaces_right;
            
            /* code modified by LLM (iteration 1): assertion to help verification */
            assert |res[i]| == left_padding + |input[i]| + right_padding == width;
            assert res[i][(width - |input[i]|+1)/2..(width - |input[i]|+1)/2 + |input[i]|] == input[i];
        }
    }
}