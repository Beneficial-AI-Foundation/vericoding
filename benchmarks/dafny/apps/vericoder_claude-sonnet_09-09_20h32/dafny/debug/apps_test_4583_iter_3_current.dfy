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
lemma ExhaustiveSearchComplete(input: string)
    requires ValidInput(input)
    requires SolutionExists(input)
    ensures exists op1, op2, op3 :: op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'} &&
        var a := CharToDigit(input[0]);
        var b := CharToDigit(input[1]);
        var c := CharToDigit(input[2]);
        var d := CharToDigit(input[3]);
        EvaluateExpression(a, b, c, d, op1, op2, op3) == 7
{
    // This follows directly from SolutionExists(input)
}

lemma ValidOutputProperties(result: string, input: string, op1: char, op2: char, op3: char)
    requires ValidInput(input)
    requires op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'}
    requires var a := CharToDigit(input[0]);
             var b := CharToDigit(input[1]);
             var c := CharToDigit(input[2]);
             var d := CharToDigit(input[3]);
             EvaluateExpression(a, b, c, d, op1, op2, op3) == 7
    requires result == [input[0], op1, input[1], op2, input[2], op3, input[3], '=', '7', '\n']
    ensures ValidOutput(result, input)
{
    assert |result| == 10;
    assert result[7..9] == "=7";
    assert result[9] == '\n';
    assert result[0] == input[0];
    assert result[2] == input[1];
    assert result[4] == input[2];
    assert result[6] == input[3];
    assert result[1] == op1 && result[3] == op2 && result[5] == op3;
}

ghost predicate SearchedAll(a: int, b: int, c: int, d: int, upToI: int, upToJ: int, upToK: int)
{
    forall i, j, k :: 0 <= i < upToI || (i == upToI && 0 <= j < upToJ) || (i == upToI && j == upToJ && 0 <= k < upToK) ==>
        var operators := ['+', '-'];
        var op1 := operators[i];
        var op2 := operators[j];
        var op3 := operators[k];
        EvaluateExpression(a, b, c, d, op1, op2, op3) != 7
}
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
    
    var operators := ['+', '-'];
    
    for i := 0 to 2
        invariant 0 <= i <= 2
        invariant SearchedAll(a, b, c, d, i, 0, 0)
    {
        var op1 := operators[i];
        for j := 0 to 2
            invariant 0 <= j <= 2
            invariant SearchedAll(a, b, c, d, i, j, 0)
        {
            var op2 := operators[j];
            for k := 0 to 2
                invariant 0 <= k <= 2
                invariant SearchedAll(a, b, c, d, i, j, k)
            {
                var op3 := operators[k];
                if EvaluateExpression(a, b, c, d, op1, op2, op3) == 7 {
                    result := [input[0], op1, input[1], op2, input[2], op3, input[3], '=', '7', '\n'];
                    ValidOutputProperties(result, input, op1, op2, op3);
                    return;
                }
            }
        }
    }
    
    assert SearchedAll(a, b, c, d, 2, 0, 0);
    assert forall op1, op2, op3 :: op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'} ==>
        EvaluateExpression(a, b, c, d, op1, op2, op3) != 7;
    ExhaustiveSearchComplete(input);
    assert false;
}
// </vc-code>

