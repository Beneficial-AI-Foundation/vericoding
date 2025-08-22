//ATOM pow
function pow(base: int, exponent: int): int
 requires exponent >= 0
{
 if exponent == 0 then 1
 else if exponent % 2 == 0 then pow(base * base, exponent / 2)
 else base * pow(base, exponent - 1)
}

//IMPL do_algebra
method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
 requires operators != [] && operands != [] && |operators| + 1 == |operands|
 requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
    var current_operands := operands;
    var i := 0;
    
    while i < |operators|
        invariant 0 <= i <= |operators|
        /* code modified by LLM (iteration 1): corrected invariant - each iteration reduces operands by 1 */
        invariant |current_operands| == |operands| - i
        invariant current_operands != []
        /* code modified by LLM (iteration 1): strengthened invariant using the relationship between operators and operands */
        invariant |current_operands| == |operators| - i + 1
        /* code modified by LLM (iteration 1): added invariant to ensure sufficient operands for next operation */
        invariant i < |operators| ==> |current_operands| >= 2
    {
        var op := operators[i];
        /* code modified by LLM (iteration 1): added assertion to help verify array access bounds */
        assert |current_operands| >= 2;
        var left := current_operands[0];
        var right := current_operands[1];
        var op_result: int;
        
        if op == '+' {
            op_result := left + right;
        } else if op == '-' {
            op_result := left - right;
        } else if op == '*' {
            op_result := left * right;
        } else if op == '/' && right != 0 {
            op_result := left / right;
        } else if op == '^' && right >= 0 {
            op_result := pow(left, right);
        } else {
            op_result := 1;
        }
        
        /* code modified by LLM (iteration 1): added assertion to verify slice operation bounds */
        assert |current_operands| >= 2;
        current_operands := [op_result] + current_operands[2..];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to verify final array has exactly one element */
    assert |current_operands| == 1;
    result := current_operands[0];
}