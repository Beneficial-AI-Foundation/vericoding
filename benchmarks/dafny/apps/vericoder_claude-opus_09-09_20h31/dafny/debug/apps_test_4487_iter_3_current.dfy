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

// <vc-helpers>
function SplitOnSpaces(s: string): seq<string>
{
    SplitOnSpacesHelper(s, 0, 0, [])
}

function SplitOnSpacesHelper(s: string, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then acc
        else acc + [s[start..i]]
    else if s[i] == ' ' then
        if start == i then
            SplitOnSpacesHelper(s, i+1, i+1, acc)
        else
            SplitOnSpacesHelper(s, i+1, i+1, acc + [s[start..i]])
    else
        SplitOnSpacesHelper(s, start, i+1, acc)
}

method SplitOnSpacesMethod(s: string) returns (parts: seq<string>)
    ensures parts == SplitOnSpaces(s)
{
    var start := 0;
    var i := 0;
    parts := [];
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant parts == SplitOnSpacesHelper(s, 0, start, [])
        invariant SplitOnSpacesHelper(s, start, i, parts) == SplitOnSpaces(s)
    {
        if s[i] == ' ' {
            if start < i {
                parts := parts + [s[start..i]];
            }
            start := i + 1;
        }
        i := i + 1;
    }
    
    if start < i {
        parts := parts + [s[start..i]];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedResult(input)
    ensures result == "YES\n" || result == "NO\n" || result == ""
// </vc-spec>
// <vc-code>
{
    var stripped: string;
    if |input| > 0 && input[|input|-1] == '\n' {
        stripped := input[0..|input|-1];
    } else {
        stripped := input;
    }
    
    var parts := SplitOnSpacesMethod(stripped);
    
    if |parts| == 3 && |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0 {
        if parts[0][|parts[0]|-1] == parts[1][0] && parts[1][|parts[1]|-1] == parts[2][0] {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    } else {
        result := "";
    }
}
// </vc-code>

