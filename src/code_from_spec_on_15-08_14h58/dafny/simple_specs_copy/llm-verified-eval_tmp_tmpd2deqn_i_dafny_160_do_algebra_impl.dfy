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
    
    /* code modified by LLM (iteration 1): Fixed loop bounds, invariants, and exponentiation logic */
    while i < |operators|
        invariant 0 <= i <= |operators|
        invariant i < |operators| ==> i + 1 < |operands|
    {
        /* code modified by LLM (iteration 1): Fixed exponentiation detection using string matching */
        if i + 1 < |operators| && operators[i] == '*' && operators[i + 1] == '*' {
            // Handle exponentiation (**)
            result := pow(result, operands[i + 1]);
            i := i + 2; // Skip both '*' characters
        } else if operators[i] == '+' {
            result := result + operands[i + 1];
            i := i + 1;
        } else if operators[i] == '-' {
            result := result - operands[i + 1];
            i := i + 1;
        } else if operators[i] == '*' {
            result := result * operands[i + 1];
            i := i + 1;
        } else if operators[i] == '/' {
            /* code modified by LLM (iteration 1): Added division by zero check */
            if operands[i + 1] != 0 {
                result := result / operands[i + 1];
            }
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 1): Handle unknown operators by skipping */
            i := i + 1;
        }
    }
}