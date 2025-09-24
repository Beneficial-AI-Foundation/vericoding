// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| >= 3 && '\n' in s && exists i :: 0 <= i < |s| - 1 && s[i] == '\n'
}

predicate ValidBinaryString(binary: string)
{
    forall c :: c in binary ==> c == '0' || c == '1'
}

predicate ValidDecimalOutput(result: string)
{
    forall c :: c in result ==> c in "0123456789"
}

function CorrectDecoding(binary: string): string
    ensures ValidDecimalOutput(CorrectDecoding(binary))
{
    var segments := splitByZero(binary);
    joinLengths(segments)
}
// </vc-preamble>

// <vc-helpers>
function extractSecondLine(s: string): string
    requires '\n' in s
    requires exists i :: 0 <= i < |s| - 1 && s[i] == '\n'
{
    var newlinePos := findNewline(s, 0);
    if newlinePos + 1 < |s| then
        extractUntilNewline(s, newlinePos + 1)
    else
        ""
}

function findNewline(s: string, start: nat): nat
    requires start <= |s|
    ensures findNewline(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else findNewline(s, start + 1)
}

function extractUntilNewline(s: string, start: nat): string
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then ""
    else if s[start] == '\n' then ""
    else [s[start]] + extractUntilNewline(s, start + 1)
}

function splitByZero(s: string): seq<string>
{
    splitByZeroHelper(s, 0, "")
}

function splitByZeroHelper(s: string, pos: nat, current: string): seq<string>
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then
        if |current| > 0 then [current] else []
    else if s[pos] == '0' then
        (if |current| > 0 then [current] else [""]) + splitByZeroHelper(s, pos + 1, "")
    else
        splitByZeroHelper(s, pos + 1, current + [s[pos]])
}

function joinLengths(segments: seq<string>): string
    ensures forall c :: c in joinLengths(segments) ==> c in "0123456789"
{
    if |segments| == 0 then ""
    else intToString(|segments[0]|) + joinLengths(segments[1..])
}

function intToString(n: nat): string
    ensures forall c :: c in intToString(n) ==> c in "0123456789"
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else intToString(n / 10) + intToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidDecimalOutput(result)
    ensures result == CorrectDecoding(extractSecondLine(s))
// </vc-spec>
// <vc-code>
{
    var binaryString := extractSecondLine(s);
    result := CorrectDecoding(binaryString);
}
// </vc-code>
