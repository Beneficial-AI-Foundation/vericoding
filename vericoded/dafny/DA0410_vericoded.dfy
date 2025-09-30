predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
function split(s: string, delimiter: char): seq<string>
{
    splitHelper(s, delimiter, 0, 0, [])
}

function splitHelper(s: string, delimiter: char, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current == |s| then
        acc + [s[start..current]]
    else if s[current] == delimiter then
        splitHelper(s, delimiter, current + 1, current + 1, acc + [s[start..current]])
    else
        splitHelper(s, delimiter, start, current + 1, acc)
}

predicate isValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] == '-' ==> |s| > 1) &&
    forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseInteger(s: string): int
    requires isValidInteger(s)
{
    if s[0] == '-' then
        -parsePositive(s[1..])
    else
        parsePositive(s)
}

function parsePositive(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else
        parsePositive(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function intToString(n: int): string
{
    if n < 0 then
        "-" + intToStringPositive(-n)
    else if n == 0 then
        "0"
    else
        intToStringPositive(n)
}

function intToStringPositive(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then
        [(n + '0' as int) as char]
    else
        intToStringPositive(n / 10) + [((n % 10) + '0' as int) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    if ValidCommandInput(input) {
        var n := ExtractN(input);
        result := intToString(n + 1) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

