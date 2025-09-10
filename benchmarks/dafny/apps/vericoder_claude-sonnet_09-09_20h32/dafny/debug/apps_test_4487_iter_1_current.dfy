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
    if |s| == 0 then []
    else
        var firstSpace := FindFirstSpace(s, 0);
        if firstSpace == -1 then [s]
        else
            var word := s[0..firstSpace];
            var rest := s[firstSpace+1..];
            [word] + SplitOnSpaces(rest)
}

function FindFirstSpace(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindFirstSpace(s, start + 1)
}

lemma SplitOnSpacesCorrect(s: string)
    ensures var parts := SplitOnSpaces(s);
            forall i :: 0 <= i < |parts| ==> |parts[i]| >= 0
{
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
    var stripped := if |input| > 0 && input[|input|-1] == '\n' then input[0..|input|-1] else input;
    var parts := SplitOnSpaces(stripped);
    
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

