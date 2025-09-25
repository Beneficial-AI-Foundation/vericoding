// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 1 && 
    IsValidInt(lines[0]) &&
    (var T := ParseInt(lines[0]);
     T >= 1 && T <= 100 &&
     |lines| >= T + 1 &&
     forall i :: 1 <= i <= T && i < |lines| ==> 
        (var parts := SplitBySpace(lines[i]);
         |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1]) &&
         ParseInt(parts[0]) >= 0 && ParseInt(parts[0]) <= 1000000000 &&
         ParseInt(parts[1]) >= 3 && ParseInt(parts[1]) <= 1000000000))
}

predicate ValidOutput(output: string)
{
    var lines := SplitByNewline(output);
    forall i :: 0 <= i < |lines| ==> lines[i] in {"Alice", "Bob"}
}

function ComputeExpectedOutput(input: string): string
    requires ValidInput(input)
{
    var lines := SplitByNewline(input);
    var T := ParseInt(lines[0]);
    var results := seq(T, i requires 0 <= i < T => 
        if i + 1 < |lines| then
            var parts := SplitBySpace(lines[i + 1]);
            if |parts| >= 2 then
                var n := ParseInt(parts[0]);
                var k := ParseInt(parts[1]);
                ComputeWinner(n, k)
            else "Alice"
        else "Alice"
    );
    JoinWithNewlines(results)
}

function ComputeWinner(n: int, k: int): string
    requires k >= 3
    ensures ComputeWinner(n, k) in {"Alice", "Bob"}
{
    if k % 3 != 0 then
        if n % 3 == 0 then "Bob" else "Alice"
    else
        var new_n := n % (k + 1);
        if new_n == k then "Alice"
        else if new_n % 3 == 0 then "Bob"
        else "Alice"
}
// </vc-preamble>

// <vc-helpers>
predicate IsValidInt(s: string)
{
    |s| > 0 && (s[0] == '-' || ('0' <= s[0] <= '9')) &&
    forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitByNewline(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, '\n');
        if pos == -1 then [s]
        else if pos < |s| then [s[..pos]] + SplitByNewline(s[pos+1..])
        else [s]
}

function SplitBySpace(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var trimmed := TrimSpaces(s);
        if |trimmed| == 0 then []
        else if |trimmed| <= |s| then
            var pos := FindChar(trimmed, ' ');
            if pos == -1 then [trimmed]
            else if pos < |trimmed| then [trimmed[..pos]] + SplitBySpace(trimmed[pos+1..])
            else [trimmed]
        else []
}

function TrimSpaces(s: string): string
    decreases |s|
    ensures |TrimSpaces(s)| <= |s|
{
    if |s| == 0 then ""
    else if s[0] == ' ' then TrimSpaces(s[1..])
    else if s[|s|-1] == ' ' then TrimSpaces(s[..|s|-1])
    else s
}

function FindChar(s: string, c: char): int
    ensures FindChar(s, c) == -1 || (0 <= FindChar(s, c) < |s|)
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else
        var rest := FindChar(s[1..], c);
        if rest == -1 then -1 else rest + 1
}

function ParseInt(s: string): int
    requires IsValidInt(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -ParsePositiveInt(s[1..])
    else ParsePositiveInt(s)
}

function ParsePositiveInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else ParsePositiveInt(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
}

function CharToDigit(c: char): int
    requires '0' <= c <= '9'
{
    c as int - '0' as int
}

function JoinWithNewlines(lines: seq<string>): string
    decreases |lines|
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + JoinWithNewlines(lines[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures result == ComputeExpectedOutput(input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    assert ValidInput(input);
    assert |lines| >= 1;

    var T := ParseInt(lines[0]);
    var output: seq<string> := [];

    var i := 1;
    while i <= T
        invariant 1 <= i <= T + 1
        invariant i <= |lines|
        invariant |output| == i - 1
        invariant forall j :: 0 <= j < |output| ==> output[j] in {"Alice", "Bob"}
        invariant forall j :: 0 <= j < i - 1 ==> 
            (var parts := SplitBySpace(lines[j + 1]);
             |parts| >= 2 ==> 
                (var n := ParseInt(parts[0]);
                 var k := ParseInt(parts[1]);
                 output[j] == ComputeWinner(n, k)))
        invariant i - 1 <= T
        invariant i <= |lines|
    {
        var parts := SplitBySpace(lines[i]);
        if |parts| >= 2 {
            var n := ParseInt(parts[0]);
            var k := ParseInt(parts[1]);

            var winner: string := ComputeWinner(n, k);
            output := output + [winner];
        } else {
            output := output + ["Alice"];
        }
        i := i + 1;
    }

    result := JoinWithNewlines(output);
}
// </vc-code>
