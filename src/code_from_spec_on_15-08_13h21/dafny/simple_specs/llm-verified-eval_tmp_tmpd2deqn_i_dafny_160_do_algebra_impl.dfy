//ATOM
/* code modified by LLM (iteration 1): Added decreases clause to prove termination */
function pow(base: int, exponent: int): int
 requires exponent >= 0
 decreases exponent
{
 if exponent == 0 then 1
 else if exponent % 2 == 0 then pow(base * base, exponent / 2)
 else base * pow(base, exponent - 1)
}

//IMPL
method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
 requires operators != [] && operands != [] && |operators| + 1 == |operands|
 requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
    result := operands[0];
    var i := 0;
    
    while i < |operators|
        invariant 0 <= i <= |operators|
    {
        var op := operators[i];
        var operand := operands[i + 1];
        
        if op == '+' {
            result := result + operand;
        } else if op == '-' {
            result := result - operand;
        } else if op == '*' {
            result := result * operand;
        } else if op == '/' && operand != 0 {
            result := result / operand;
        } else if op == '^' {
            result := pow(result, operand);
        }
        
        i := i + 1;
    }
}