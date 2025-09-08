Read an integer N from input. If N=1, print "Hello World". If N=2, read two additional integers A and B, then print their sum.
Constraints: N is 1 or 2, A and B are integers between 1 and 9 (inclusive).

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

function ExpectedOutput(stdin_input: string): string
{
    var lines := SplitLinesFunc(stdin_input);
    if |lines| >= 1 then
        var n := StringToInt(lines[0]);
        if n == 1 then "Hello World\n"
        else if n != 1 && |lines| >= 3 then
            var a := StringToInt(lines[1]);
            var b := StringToInt(lines[2]);
            IntToString(a + b) + "\n"
        else ""
    else ""
}

function SplitLinesFunc(s: string): seq<string>
{
    SplitLinesFuncHelper(s, 0, "", [])
}

function SplitLinesFuncHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if current == "" then acc else acc + [current]
    else if s[i] == '\n' then
        SplitLinesFuncHelper(s, i + 1, "", acc + [current])
    else
        SplitLinesFuncHelper(s, i + 1, current + [s[i]], acc)
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
    else StringToIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]
}

method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| >= 0
    ensures forall i :: 0 <= i < |lines| ==> '\n' !in lines[i]
    ensures lines == SplitLinesFunc(s)
{
    lines := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |lines| ==> '\n' !in lines[j]
        invariant '\n' !in current
        invariant SplitLinesFuncHelper(s, i, current, lines) == SplitLinesFunc(s)
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    if current != "" {
        lines := lines + [current];
    }
}

method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == ExpectedOutput(stdin_input)
{
    var lines := SplitLines(stdin_input);
    if |lines| == 0 {
        result := "";
        return;
    }

    var n := StringToInt(lines[0]);

    if n == 1 {
        result := "Hello World\n";
    } else if n != 1 && |lines| >= 3 {
        var a := StringToInt(lines[1]);
        var b := StringToInt(lines[2]);
        var tmpCall1 := IntToString(a + b);
        result := tmpCall1 + "\n";
    } else {
        result := "";
    }
}
