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

  var op1, op2, op3 :| 
    op1 in {'+', '-'} && op2 in {'+', '-'} && op3 in {'+', '-'} &&
    EvaluateExpression(a, b, c, d, op1, op2, op3) == 7;

  var arr := new char[10];
  arr[0] := input[0];
  arr[1] := op1;
  arr[2] := input[1];
  arr[3] := op2;
  arr[4] := input[2];
  arr[5] := op3;
  arr[6] := input[3];
  arr[7] := '=';
  arr[8] := '7';
  arr[9] := '\n';

  result := new string(arr);
}
// </vc-code>

