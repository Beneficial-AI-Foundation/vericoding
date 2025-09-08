Compare two large positive integers A and B and determine their relative magnitude.
Input consists of two positive integers on separate lines, each up to 100 digits.
Output "GREATER" if A > B, "LESS" if A < B, or "EQUAL" if A = B.

predicate ValidInput(input: string)
{
    var lines := SplitLinesSpec(input);
    |lines| >= 2 && IsValidInteger(lines[0]) && IsValidInteger(lines[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLinesSpec(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then SplitLinesSpec(s[1..])
    else 
        var nextNewline := FindNextNewline(s, 0);
        if nextNewline == -1 then [s]
        else 
            assert nextNewline >= 0 && nextNewline < |s|;
            [s[0..nextNewline]] + SplitLinesSpec(s[nextNewline+1..])
}

function FindNextNewline(s: string, start: nat): int
    requires start <= |s|
    decreases |s| - start
    ensures FindNextNewline(s, start) == -1 || (start <= FindNextNewline(s, start) < |s|)
    ensures FindNextNewline(s, start) != -1 ==> s[FindNextNewline(s, start)] == '\n'
    ensures FindNextNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
    ensures FindNextNewline(s, start) != -1 ==> forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function ParseIntSpec(s: string): int
    requires IsValidInteger(s)
{
    ParseIntHelper(s, 0)
}

function ParseIntHelper(s: string, pos: nat): int
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| || s[pos] == '\n' || s[pos] == '\r' then 0
    else if '0' <= s[pos] <= '9' then
        (s[pos] as int - '0' as int) + 10 * ParseIntHelper(s, pos + 1)
    else
        ParseIntHelper(s, pos + 1)
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesSpec(s)
{
    if |s| == 0 {
        lines := [];
        return;
    }

    if s[0] == '\n' {
        lines := SplitLines(s[1..]);
        return;
    }

    var nextNewline := FindNextNewlineImpl(s, 0);
    if nextNewline == -1 {
        lines := [s];
    } else {
        assert nextNewline >= 0 && nextNewline < |s|;
        var rest := SplitLines(s[nextNewline+1..]);
        lines := [s[0..nextNewline]] + rest;
    }
}

method FindNextNewlineImpl(s: string, start: nat) returns (result: int)
    requires start <= |s|
    ensures result == FindNextNewline(s, start)
    ensures result == -1 || (start <= result < |s|)
    ensures result != -1 ==> s[result] == '\n'
    ensures result == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
{
    var i := start;
    while i < |s|
        invariant start <= i <= |s|
        invariant forall j :: start <= j < i ==> s[j] != '\n'
        decreases |s| - i
    {
        if s[i] == '\n' {
            result := i;
            return;
        }
        i := i + 1;
    }
    result := -1;
}

method ParseInt(s: string) returns (n: int)
    requires IsValidInteger(s)
    ensures n == ParseIntSpec(s)
{
    n := 0;
    var i := |s|;

    while i > 0
        invariant 0 <= i <= |s|
        invariant n == ParseIntHelper(s, i)
        decreases i
    {
        i := i - 1;
        if i < |s| && s[i] != '\n' && s[i] != '\r' && '0' <= s[i] <= '9' {
            n := (s[i] as int - '0' as int) + 10 * n;
        }
    }
}

method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==>
        var lines := SplitLinesSpec(input);
        var a := ParseIntSpec(lines[0]);
        var b := ParseIntSpec(lines[1]);
        (result == "LESS\n" <==> a < b) &&
        (result == "GREATER\n" <==> a > b) &&
        (result == "EQUAL\n" <==> a == b)
    ensures !ValidInput(input) ==> result == ""
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        return "";
    }

    if !IsValidInteger(lines[0]) || !IsValidInteger(lines[1]) {
        return "";
    }

    var a := ParseInt(lines[0]);
    var b := ParseInt(lines[1]);

    if a < b {
        result := "LESS\n";
    } else if a > b {
        result := "GREATER\n";
    } else {
        result := "EQUAL\n";
    }
}
