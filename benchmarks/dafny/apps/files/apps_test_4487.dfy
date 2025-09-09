Given three strings A, B, and C, determine if they form a word chain.
A word chain exists if the last character of A equals the first character of B
and the last character of B equals the first character of C.
Output "YES" if both conditions are true, "NO" otherwise.

predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidParsedInput(parts: seq<string>)
{
    |parts| == 3 && |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
}

predicate IsWordChain(a: string, b: string, c: string)
    requires |a| > 0 && |b| > 0 && |c| > 0
{
    a[|a|-1] == b[0] && b[|b|-1] == c[0]
}

function ExpectedResult(input: string): string
    requires ValidInput(input)
{
    var stripped := if |input| > 0 && input[|input|-1] == '\n' then input[0..|input|-1] else input;
    var parts := SplitOnSpaces(stripped);
    if ValidParsedInput(parts) then
        if IsWordChain(parts[0], parts[1], parts[2]) then "YES\n" else "NO\n"
    else
        ""
}

function SplitOnSpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitOnSpacesHelper(s, 0, [])
}

function SplitOnSpacesHelper(s: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then acc
    else 
        var nextSpace := FindSpaceFrom(s, start);
        if nextSpace == -1 then
            acc + [s[start..]]
        else
            SplitOnSpacesHelper(s, nextSpace + 1, acc + [s[start..nextSpace]])
}

function FindSpaceFrom(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures FindSpaceFrom(s, start) == -1 || (start <= FindSpaceFrom(s, start) < |s| && s[FindSpaceFrom(s, start)] == ' ')
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpaceFrom(s, start + 1)
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedResult(input)
    ensures result == "YES\n" || result == "NO\n" || result == ""
{
    var stripped := if |input| > 0 && input[|input|-1] == '\n' then input[0..|input|-1] else input;
    var parts := SplitOnSpaces(stripped);

    if |parts| != 3 || |parts[0]| == 0 || |parts[1]| == 0 || |parts[2]| == 0 {
        return "";
    }

    if parts[0][|parts[0]|-1] == parts[1][0] && parts[1][|parts[1]|-1] == parts[2][0] {
        return "YES\n";
    } else {
        return "NO\n";
    }
}
