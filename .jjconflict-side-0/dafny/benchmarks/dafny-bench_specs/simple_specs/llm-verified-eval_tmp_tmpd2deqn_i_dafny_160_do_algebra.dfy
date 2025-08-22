//ATOM
function pow(base: int, exponent: int): int
 requires exponent >= 0
{
 if exponent == 0 then 1
 else if exponent % 2 == 0 then pow(base * base, exponent / 2)
 else base * pow(base, exponent - 1)
}


// SPEC

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
 requires operators != [] && operands != [] && |operators| + 1 == |operands|
 requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
}
