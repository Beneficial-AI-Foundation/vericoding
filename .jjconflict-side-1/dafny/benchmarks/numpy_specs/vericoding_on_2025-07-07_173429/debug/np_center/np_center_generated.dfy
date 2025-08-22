//IMPL
method center (input: array<string>, width:nat) returns (res: array<string>)
    requires forall i :: 0 <= i < input.Length ==> |input[i]| >= 1
    ensures res.Length == input.Length 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| > width then |res[i]| == |input[i]| else |res[i]| == width 
    ensures forall i :: 0 <= i < input.Length ==> 
    if |input[i]| < width then res[i][(width - |input[i]|+1)/2..((width - |input[i]|+1)/2 + |input[i]| -1)] == input[i] else true
{
    res := new string[input.Length];
    
    for i := 0 to input.Length
        invariant res.Length == input.Length
        invariant forall j :: 0 <= j < i ==> if |input[j]| > width then |res[j]| == |input[j]| else |res[j]| == width
        invariant forall j :: 0 <= j < i ==> 
            if |input[j]| < width then res[j][(width - |input[j]|+1)/2..((width - |input[j]|+1)/2 + |input[j]| -1)] == input[j] else true
    {
        if |input[i]| >= width {
            res[i] := input[i];
        } else {
            var padding := width - |input[i]|;
            var leftPad := (padding + 1) / 2;
            var rightPad := padding - leftPad;
            
            var spaces := seq(leftPad, _ => ' ');
            var rightSpaces := seq(rightPad, _ => ' ');
            
            res[i] := spaces + input[i] + rightSpaces;
        }
    }
}