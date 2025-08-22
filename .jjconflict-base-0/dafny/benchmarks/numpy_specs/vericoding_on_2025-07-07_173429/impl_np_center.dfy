//IMPL
method center (input: array<string>, width:nat) returns (res: array<string>)
    requires forall i :: 0 <= i < input.Length ==> |input[i]| >= 1
    ensures res.Length == input.Length 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| > width then |res[i]| == |input[i]| else |res[i]| == width 
    ensures forall i :: 0 <= i < input.Length ==> 
    if |input[i]| < width then res[i][(width - |input[i]|+1)/2..((width - |input[i]|+1)/2 + |input[i]|)] == input[i] else true
{
    res := new string[input.Length];
    
    for i := 0 to input.Length
        invariant res.Length == input.Length
        invariant forall j :: 0 <= j < i ==> if |input[j]| > width then |res[j]| == |input[j]| else |res[j]| == width
        invariant forall j :: 0 <= j < i ==> 
            if |input[j]| < width then res[j][(width - |input[j]|+1)/2..((width - |input[j]|+1)/2 + |input[j]|)] == input[j] else true
    {
        if |input[i]| >= width {
            res[i] := input[i];
        } else {
            /* code modified by LLM (iteration 1): Fixed padding calculation and added assertions for verification */
            var padding := width - |input[i]|;
            var leftPad := (padding + 1) / 2;
            var rightPad := padding - leftPad;
            
            assert leftPad + rightPad == padding;
            assert leftPad + rightPad + |input[i]| == width;
            
            var spaces := seq(leftPad, _ => ' ');
            var rightSpaces := seq(rightPad, _ => ' ');
            
            res[i] := spaces + input[i] + rightSpaces;
            
            /* code modified by LLM (iteration 1): Added assertion to help verify the substring property */
            assert |res[i]| == leftPad + |input[i]| + rightPad;
            assert |res[i]| == width;
            assert leftPad == (width - |input[i]| + 1) / 2;
            assert res[i][leftPad..leftPad + |input[i]|] == input[i];
            assert leftPad == (width - |input[i]| + 1) / 2;
            assert res[i][(width - |input[i]| + 1) / 2..(width - |input[i]| + 1) / 2 + |input[i]|] == input[i];
        }
    }
}