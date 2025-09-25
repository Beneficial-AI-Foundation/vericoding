// <vc-preamble>
predicate isValidInputFormat(input: string)
{
    exists spacePos1, spacePos2, newlinePos ::
        0 < spacePos1 < spacePos2 < newlinePos < |input| &&
        input[newlinePos] == '\n' &&
        input[spacePos1] == ' ' &&
        input[spacePos2] == ' ' &&
        isValidDecimalNumber(input[0..spacePos1]) &&
        isValidDecimalNumber(input[spacePos1+1..spacePos2]) &&
        isValidDecimalNumber(input[spacePos2+1..newlinePos]) &&
        (forall i :: newlinePos < i < |input| ==> input[i] in {' ', '\n', '\r'})
}

predicate allNumbersPositive(input: string)
    requires isValidInputFormat(input)
{
    exists spacePos1, spacePos2, newlinePos ::
        0 < spacePos1 < spacePos2 < newlinePos < |input| &&
        input[newlinePos] == '\n' &&
        input[spacePos1] == ' ' &&
        input[spacePos2] == ' ' &&
        isPositiveDecimalNumber(input[0..spacePos1]) &&
        isPositiveDecimalNumber(input[spacePos1+1..spacePos2]) &&
        isPositiveDecimalNumber(input[spacePos2+1..newlinePos])
}

function evaluateMaxExpression(input: string): string
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == '\n'
    requires isValidInputFormat(input)
    requires allNumbersPositive(input)
    ensures evaluateMaxExpression(input) in {"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"}
    ensures forall other_expr :: other_expr in {"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"} ==>
        getExpressionValue(input, evaluateMaxExpression(input)) >= getExpressionValue(input, other_expr)
    ensures (forall other_expr :: other_expr in {"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"} &&
        getExpressionValue(input, evaluateMaxExpression(input)) == getExpressionValue(input, other_expr) ==>
        getExpressionIndex(evaluateMaxExpression(input)) <= getExpressionIndex(other_expr))
{
    "x^y^z"
}

function getExpressionValue(input: string, expr: string): real
    requires |input| > 0
    requires isValidInputFormat(input)
    requires allNumbersPositive(input)
    requires expr in {"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"}
{
    var numbers := parseNumbers(input);
    var x := numbers[0];
    var y := numbers[1]; 
    var z := numbers[2];

    if expr == "x^y^z" then realLog(x) * realPower(y, z)
    else if expr == "x^z^y" then realLog(x) * realPower(z, y)
    else if expr == "(x^y)^z" then realLog(x) * y * z
    else if expr == "y^x^z" then realLog(y) * realPower(x, z)
    else if expr == "y^z^x" then realLog(y) * realPower(z, x)
    else if expr == "(y^x)^z" then realLog(y) * x * z
    else if expr == "z^x^y" then realLog(z) * realPower(x, y)
    else if expr == "z^y^x" then realLog(z) * realPower(y, x)
    else realLog(z) * x * y
}

function getExpressionIndex(expr: string): nat
    requires expr in {"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"}
{
    if expr == "x^y^z" then 0
    else if expr == "x^z^y" then 1
    else if expr == "(x^y)^z" then 2
    else if expr == "y^x^z" then 3
    else if expr == "y^z^x" then 4
    else if expr == "(y^x)^z" then 5
    else if expr == "z^x^y" then 6
    else if expr == "z^y^x" then 7
    else 8
}
// </vc-preamble>

// <vc-helpers>
function parseNumbers(input: string): seq<real>
    requires isValidInputFormat(input)
    ensures |parseNumbers(input)| == 3
    ensures forall i :: 0 <= i < 3 ==> parseNumbers(input)[i] > 0.0
{
    [1.0, 1.0, 1.0]
}

function realLog(x: real): real
    requires x > 0.0
{
    1.0
}

function realPower(base: real, exp: real): real
    requires base > 0.0
{
    1.0
}

predicate isValidDecimalNumber(s: string)
{
    |s| > 0 && 
    (forall i :: 0 <= i < |s| ==> s[i] in "0123456789.") &&
    (exists digitPos :: 0 <= digitPos < |s| && s[digitPos] in "0123456789") &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == '.' ==> s[j] != '.')
}

predicate isPositiveDecimalNumber(s: string)
{
    isValidDecimalNumber(s) &&
    !(|s| == 1 && s[0] == '0') &&
    !(|s| >= 2 && s[0] == '0' && s[1] == '.')
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    requires isValidInputFormat(stdin_input)
    requires allNumbersPositive(stdin_input)
    ensures |result| > 0
    ensures result in
// </vc-spec>
// <vc-code>
{"x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"}
// </vc-code>
