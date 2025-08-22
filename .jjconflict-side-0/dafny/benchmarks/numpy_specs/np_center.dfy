//SPEC
method center (input: array<string>, width:nat) returns (res: array<string>)
    requires forall i :: 0 <= i < input.Length ==> |input[i]| >= 1
    ensures res.Length == input.Length 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| > width then |res[i]| == |input[i]| else |res[i]| == width 
    ensures forall i :: 0 <= i < input.Length ==> 
    if |input[i]| < width then res[i][(width - |input[i]|+1)/2..((width - |input[i]|+1)/2 + |input[i]| -1)] == input[i] else true
{}