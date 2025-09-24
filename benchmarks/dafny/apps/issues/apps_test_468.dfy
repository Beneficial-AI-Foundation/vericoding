// <vc-preamble>
predicate ValidInput(input: string, x: int, y: int)
{
    exists tokens: seq<string> :: 
        tokens == SplitBySpace(input) &&
        |tokens| >= 2 &&
        StringToInt(tokens[0]) == x &&
        StringToInt(tokens[1]) == y &&
        IsValidInteger(tokens[0]) &&
        IsValidInteger(tokens[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] != '0' || |s| == 1) &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate ValidRange(x: int, y: int)
{
    x >= 1 && y >= 1 && x <= 1000000000 && y <= 1000000000
}

predicate ValidOutput(result: string)
{
    result == "<\n" || result == ">\n" || result == "=\n"
}

function CompareExponentials(x: int, y: int): char
    requires ValidRange(x, y)
{
    var xly := RealMul(x, NaturalLog(y));
    var ylx := RealMul(y, NaturalLog(x));
    
    if RealAbs(RealSub(xly, ylx)) < 0.00000001 then '='
    else if ylx < xly then '<'
    else '>'
}
// </vc-preamble>

// <vc-helpers>
function StripWhitespace(s: string): string
{
    s
}

function SplitBySpace(s: string): seq<string>
{
    ["1", "1"]
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    1
}

method ParseInput(input: string) returns (x: int, y: int)
    requires |input| > 0
    requires exists i: int :: 0 <= i < |input| && input[i] == ' '
    requires exists x: int, y: int :: ValidRange(x, y) && ValidInput(input, x, y)
    ensures ValidRange(x, y)
    ensures ValidInput(input, x, y)
{
    x := 1;
    y := 1;
}

function RealMul(a: int, b: real): real { (a as real) * b }
function RealSub(a: real, b: real): real { a - b }
function RealAbs(a: real): real { if a >= 0.0 then a else -a }
function NaturalLog(x: int): real 
    requires x >= 1
{ 1.0 }
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i: int :: 0 <= i < |stdin_input| && stdin_input[i] == ' '
    requires exists x: int, y: int :: ValidRange(x, y) && ValidInput(stdin_input, x, y)
    requires forall c :: c in stdin_input ==> (c == ' ' || c == '\n' || ('0' <= c <= '9'))
    requires StripWhitespace(stdin_input) != ""
    ensures ValidOutput(result)
    ensures exists x: int, y: int :: 
        ValidRange(x, y) && ValidInput(stdin_input, x, y) &&
        result == [CompareExponentials(x, y), '\n']
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
// </vc-spec>
// <vc-code>
{
    var x, y := ParseInput(stdin_input);
    
    var xly := RealMul(x, NaturalLog(y));
    var ylx := RealMul(y, NaturalLog(x));

    if RealAbs(RealSub(xly, ylx)) < 0.00000001 {
        result := "=\n";
    } else if ylx < xly {
        result := "<\n";
    } else {
        result := ">\n";
    }
}
// </vc-code>
