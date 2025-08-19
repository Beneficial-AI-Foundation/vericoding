//https://numpy.org/doc/stable/reference/generated/numpy.char.center.html#numpy.char.center

// Return a copy of a with its elements centered in a string of length width.
method center (input: array<string>, width:nat) returns (res: array<string>)
    requires forall i :: 0 <= i < input.Length ==> |input[i]| >= 1;
    ensures res.Length == input.Length 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| > width then |res[i]| == |input[i]| else |res[i]| == width 
    ensures forall i :: 0 <= i < input.Length ==> if |input[i]| < width then res[i][(width - |input[i]|+1)/2..((width - |input[i]|+1)/2 + |input[i]| -1)] == input[i] else true;
    // ensures forall i, j :: 0 <= i < input.Length && 0 <= j < width ==> if j < (width - |input[i]|+1)/2 || j > (width - |input[i]|+1)/2 + input[i] -1 then res[i][j] == ' ''z else true;
    // ensures forall i :: 0 <= i < input.Length {forall j | 0 <= j < |res[i]| ==> if j < (width - |input[i]|+1)/2 || j > (width - |input[i]|+1)/2 + input[i] -1 ==> res[i][j] == " "}
{}