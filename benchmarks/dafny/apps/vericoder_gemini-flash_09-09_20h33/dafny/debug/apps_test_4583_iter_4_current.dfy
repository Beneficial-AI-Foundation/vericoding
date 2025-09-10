predicate ValidInput(input: string)
{
    |input| == 5 && |input[..4]| == 4 && 
    (forall i :: 0 <= i < 4 ==> '0' <= input[i] <= '9') &&
    input[4] == '\n'
}

function CharToDigit(c: char): int
    requires '0' <= c <= '9'
{
    (c as int) - ('0' as int)
}

function EvaluateExpression(a: int, b: int, c: int, d: int, op1: char, op2: char, op3: char): int
    requires op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'}
{
    var b_val := if op1 == '+' then b else -b;
    var c_val := if op2 == '+' then c else -c;
    var d_val := if op3 == '+' then d else -d;
    a + b_val + c_val + d_val
}

predicate SolutionExists(input: string)
    requires ValidInput(input)
{
    var a := CharToDigit(input[0]);
    var b := CharToDigit(input[1]);
    var c := CharToDigit(input[2]);
    var d := CharToDigit(input[3]);
    exists op1, op2, op3 :: op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'} &&
        EvaluateExpression(a, b, c, d, op1, op2, op3) == 7
}

predicate ValidOutput(result: string, input: string)
    requires ValidInput(input)
{
    |result| == 10 && result[7..9] == "=7" && result[9] == '\n' &&
    result[0] == input[0] && result[2] == input[1] && 
    result[4] == input[2] && result[6] == input[3] &&
    result[1] in {'+', '-'} && result[3] in {'+', '-'} && result[5] in {'+', '-'} &&
    var a := CharToDigit(input[0]);
    var b := CharToDigit(input[1]);
    var c := CharToDigit(input[2]);
    var d := CharToDigit(input[3]);
    EvaluateExpression(a, b, c, d, result[1], result[3], result[5]) == 7
}

// <vc-helpers>
// The helper functions are already defined in the preamble and do not need to be redefined here.
// Removing them from this section resolves the "Duplicate member name" errors.
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    requires SolutionExists(input)
    ensures ValidOutput(result, input)
// </vc-spec>
// <vc-code>
{
    var a := CharToDigit(input[0]);
    var b := CharToDigit(input[1]);
    var c := CharToDigit(input[2]);
    var d := CharToDigit(input[3]);

    var found_op1: char := '+';
    var found_op2: char := '+';
    var found_op3: char := '+';

    var ops := ['+', '-'];

    for op1_idx := 0 to |ops| 
    {
        var op1 := ops[op1_idx];
        for op2_idx := 0 to |ops| 
        {
            var op2 := ops[op2_idx];
            for op3_idx := 0 to |ops| 
            {
                var op3 := ops[op3_idx];
                if EvaluateExpression(a, b, c, d, op1, op2, op3) == 7 {
                    found_op1 := op1;
                    found_op2 := op2;
                    found_op3 := op3;
                    goto FoundSolution; 
                }
            }
        }
    }

    FoundSolution:
    result := "" + input[0].ToString() + found_op1.ToString() + input[1].ToString() + found_op2.ToString() + input[2].ToString() + found_op3.ToString() + input[3].ToString() + "=7\n";
}
// </vc-code>

