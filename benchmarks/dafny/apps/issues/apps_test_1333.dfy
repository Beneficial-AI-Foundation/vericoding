// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    exists space_pos :: (0 < space_pos < |trimmed| && trimmed[space_pos] == ' ' &&
    IsValidInteger(trimmed[..space_pos]) && IsValidInteger(trimmed[space_pos+1..]) &&
    var n := StringToInt(trimmed[..space_pos]);
    var m := StringToInt(trimmed[space_pos+1..]);
    3 <= n <= 50 && 3 <= m <= 50 && n % 2 == 1)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
}

predicate ValidSnakePattern(input: string, output: string)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    exists space_pos :: (0 < space_pos < |trimmed| && trimmed[space_pos] == ' ' &&
    var n := StringToInt(trimmed[..space_pos]);
    var m := StringToInt(trimmed[space_pos+1..]);
    |output| > 0 && output[|output|-1] == '\n' &&
    var content := output[..|output|-1];
    var lines := SplitLines(content);
    |lines| == n &&
    forall i :: (0 <= i < n ==>
        |lines[i]| == m &&
        (i % 2 == 0 ==> forall j :: 0 <= j < m ==> lines[i][j] == '#') &&
        (i % 4 == 1 ==> m > 0 && (forall j :: 0 <= j < m-1 ==> lines[i][j] == '.') && lines[i][m-1] == '#') &&
        (i % 4 == 3 ==> m > 0 && lines[i][0] == '#' && (forall j :: 1 <= j < m ==> lines[i][j] == '.'))))
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if '\n' !in s then [s]
    else
        var newline_pos := FindChar(s, '\n');
        if newline_pos < |s| - 1 then
            [s[..newline_pos]] + SplitLines(s[newline_pos+1..])
        else
            [s[..newline_pos]]
}

function FindChar(s: string, c: char): int
    requires c in s
    ensures 0 <= FindChar(s, c) < |s|
{
    if s[0] == c then 0 else 1 + FindChar(s[1..], c)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else StringToIntHelper(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
}

function CharToDigit(c: char): int
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == ' '
    requires ValidInputFormat(input)
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> result[i] in
// </vc-spec>
// <vc-code>
{'#', '.', '\n'}
// </vc-code>
