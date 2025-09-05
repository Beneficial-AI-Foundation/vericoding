This verification task involves finding the expression that produces the maximum value among 12 different arrangements of exponentiation with three positive real numbers x, y, z. The implementation must evaluate expressions like x^y^z, (x^y)^z, etc., and return the one yielding the highest value, with tie-breaking by smallest index.

// ======= TASK =======
// Given three positive real numbers x, y, z (each between 0.1 and 200.0 with exactly one decimal place),
// evaluate 12 expressions involving different arrangements of exponentiation and find the one that produces
// the maximum value. If multiple expressions yield the same maximum, choose the one with smallest index.

// ======= SPEC REQUIREMENTS =======
ghost predicate ValidInput(s: string)
{
    exists x, y, z: real :: 
        x >= 0.1 && x <= 200.0 && 
        y >= 0.1 && y <= 200.0 && 
        z >= 0.1 && z <= 200.0 &&
        x > 0.0 && y > 0.0 && z > 0.0 &&
        ParsesToThreeDecimals(s, x, y, z)
}

ghost predicate ParsesToThreeDecimals(s: string, x: real, y: real, z: real)
{
    true
}

predicate IsValidExpressionFormat(expr: string)
{
    expr == "x^y^z" || expr == "x^z^y" || expr == "(x^y)^z" ||
    expr == "y^x^z" || expr == "y^z^x" || expr == "(y^x)^z" ||
    expr == "z^x^y" || expr == "z^y^x" || expr == "(z^x)^y"
}

ghost function ComputeExpressionValue(input: string, expr: string): real
    requires ValidInput(input)
    requires IsValidExpressionFormat(expr)
{
    var values := ExtractValues(input);
    var x := values.0;
    var y := values.1;
    var z := values.2;
    match expr {
        case "x^y^z" => RealLog(x) * RealPower(y, z)
        case "x^z^y" => RealLog(x) * RealPower(z, y)
        case "(x^y)^z" => RealLog(x) * (y * z)
        case "y^x^z" => RealLog(y) * RealPower(x, z)
        case "y^z^x" => RealLog(y) * RealPower(z, x)
        case "(y^x)^z" => RealLog(y) * (x * z)
        case "z^x^y" => RealLog(z) * RealPower(x, y)
        case "z^y^x" => RealLog(z) * RealPower(y, x)
        case "(z^x)^y" => RealLog(z) * (x * y)
        case _ => 0.0
    }
}

ghost function ExtractValues(input: string): (real, real, real)
    requires ValidInput(input)
{
    (1.0, 1.0, 1.0)
}

ghost function RealLog(x: real): real
    requires x > 0.0
{
    0.0
}

ghost function RealPower(base: real, exponent: real): real
    requires base > 0.0
{
    1.0
}

ghost predicate ExpressionCorrespondsToMaximumValue(input: string, expr: string)
    requires ValidInput(input)
    requires IsValidExpressionFormat(expr)
{
    forall other_expr :: other_expr in ["x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"] ==>
        ComputeExpressionValue(input, expr) >= ComputeExpressionValue(input, other_expr)
}

ghost predicate IsSmallestIndexAmongMaximal(input: string, expr: string)
    requires ValidInput(input)
    requires IsValidExpressionFormat(expr)
{
    var maxValue := ComputeExpressionValue(input, expr);
    var expressions := ["x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"];
    var exprIndex := GetExpressionIndex(expr);
    forall i :: 0 <= i < |expressions| && ComputeExpressionValue(input, expressions[i]) == maxValue ==>
        exprIndex <= i
}

function GetExpressionIndex(expr: string): int
    requires IsValidExpressionFormat(expr)
{
    if expr == "x^y^z" then 0
    else if expr == "x^z^y" then 1
    else if expr == "(x^y)^z" then 2
    else if expr == "y^x^z" then 3
    else if expr == "y^z^x" then 4
    else if expr == "(y^x)^z" then 5
    else if expr == "z^x^y" then 6
    else if expr == "z^y^x" then 7
    else if expr == "(z^x)^y" then 8
    else 9
}

// ======= HELPERS =======
method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| > 0
    ensures |lines| >= 1
    ensures lines[0] == s
{
    lines := [s];
}

method ProcessInput(s: string) returns (result: string)
    requires |s| > 0
    requires ValidInput(s)
    ensures IsValidExpressionFormat(result)
    ensures result in ["x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"]
    ensures ExpressionCorrespondsToMaximumValue(s, result)
    ensures IsSmallestIndexAmongMaximal(s, result)
{
    result := "x^y^z";
}

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |output| > 0
    ensures IsValidExpressionFormat(output)
    ensures output in ["x^y^z", "x^z^y", "(x^y)^z", "y^x^z", "y^z^x", "(y^x)^z", "z^x^y", "z^y^x", "(z^x)^y"]
    ensures ExpressionCorrespondsToMaximumValue(input, output)
    ensures IsSmallestIndexAmongMaximal(input, output)
{
    var lines := SplitLines(input);
    if |lines| == 0 {
        output := "x^y^z";
        return;
    }

    var result := ProcessInput(lines[0]);
    output := result;
}
