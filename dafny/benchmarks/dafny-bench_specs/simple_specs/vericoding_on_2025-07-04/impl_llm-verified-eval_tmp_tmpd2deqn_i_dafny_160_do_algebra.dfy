//ATOM
function pow(base: int, exponent: int): int
 requires exponent >= 0
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
    /* code modified by LLM (iteration 1): Fixed loop invariants and bounds checking for exponentiation */
    while i < |operators|
        invariant 0 <= i <= |operators|
        invariant |operators| + 1 == |operands|
    {
        var op := operators[i];
        var operand := operands[i + 1];
        
        /* code modified by LLM (iteration 1): Fixed exponentiation detection with proper bounds checking */
        if op == '*' && i + 1 < |operators| && operators[i + 1] == '*' {
            // Handle ** as exponentiation
            result := pow(result, operand);
            /* code modified by LLM (iteration 1): Increment by 2 to skip both '*' characters with bounds check */
            i := i + 2;
        } else if op == '+' {
            result := result + operand;
            i := i + 1;
        } else if op == '-' {
            result := result - operand;
            i := i + 1;
        } else if op == '*' {
            result := result * operand;
            i := i + 1;
        } else {
            // For any unrecognized operator, treat as addition
            result := result + operand;
            i := i + 1;
        }
    }
}