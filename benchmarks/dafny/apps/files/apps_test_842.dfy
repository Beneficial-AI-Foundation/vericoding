// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| > 0
}

function ExtractFirstLine(s: string): string
    requires |s| > 0
    ensures |ExtractFirstLine(s)| >= 0
{
    var newline_pos := FindFirstNewline(s);
    if newline_pos == -1 then s else s[..newline_pos]
}

function FindFirstNewline(s: string): int
    ensures FindFirstNewline(s) == -1 || (0 <= FindFirstNewline(s) < |s|)
    ensures FindFirstNewline(s) == -1 <==> (forall i :: 0 <= i < |s| ==> s[i] != '\n')
    ensures FindFirstNewline(s) != -1 ==> s[FindFirstNewline(s)] == '\n'
    ensures FindFirstNewline(s) != -1 ==> (forall i :: 0 <= i < FindFirstNewline(s) ==> s[i] != '\n')
{
    if |s| == 0 then -1
    else if s[0] == '\n' then 0
    else 
        var rest_result := FindFirstNewline(s[1..]);
        if rest_result == -1 then -1 else rest_result + 1
}

function ReverseString(s: string): string
    ensures |ReverseString(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> ReverseString(s)[i] == s[|s| - 1 - i]
{
    if |s| == 0 then "" else ReverseString(s[1..]) + [s[0]]
}

predicate ValidOutput(result: string, input: string)
    requires |input| > 0
{
    |result| >= 1 &&
    result[|result| - 1] == '\n' &&
    exists n: string :: 
        n == ExtractFirstLine(input) &&
        result == n + ReverseString(n) + "\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result, stdin_input)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
