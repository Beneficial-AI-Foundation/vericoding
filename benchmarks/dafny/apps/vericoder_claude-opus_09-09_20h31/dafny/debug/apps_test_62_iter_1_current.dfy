predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    (stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input))
}

predicate ValidResult(result: string)
{
    result == "BitAryo" || result == "BitLGM"
}

function GameResult(stdin_input: string): string
    requires ValidInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    if |lines| >= 1 then
        var n := parseInt(lines[0]);
        if n == 3 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 3 then
                var xorResult := xorSequence(values);
                if xorResult == 0 then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if n == 2 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 2 && values[0] >= 0 && values[1] >= 0 then
                var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
                if goldenRatioRelation(sortedValues) then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if |lines| >= 2 then
            var value := parseInt(lines[1]);
            if value == 0 then "BitAryo" else "BitLGM"
        else "BitLGM"
    else "BitLGM"
}

// <vc-helpers>
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[|s|-1] == '\n' then [s[..|s|-1]]
    else [s]
}

function parseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -parseNat(s[1..])
    else parseNat(s)
}

function parseNat(s: string): nat
{
    if |s| == 0 then 0
    else if '0' <= s[0] <= '9' then 
        (s[0] as int - '0' as int) * pow10(|s| - 1) + parseNat(s[1..])
    else 0
}

function pow10(n: nat): nat
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

function parseInts(s: string): seq<int>
{
    parseIntsHelper(s, 0)
}

function parseIntsHelper(s: string, start: nat): seq<int>
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then []
    else
        var nextSpace := findNextSpace(s, start);
        if nextSpace == start then parseIntsHelper(s, start + 1)
        else [parseInt(s[start..nextSpace])] + parseIntsHelper(s, nextSpace)
}

function findNextSpace(s: string, start: nat): nat
    requires start <= |s|
    ensures start <= findNextSpace(s, start) <= |s|
{
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else findNextSpace(s, start + 1)
}

function xorSequence(values: seq<int>): int
{
    if |values| == 0 then 0
    else values[0] ^ xorSequence(values[1..])
}

function goldenRatioRelation(sortedValues: seq<int>): bool
    requires |sortedValues| == 2
{
    sortedValues[0] >= 0 && sortedValues[1] >= 0 &&
    sortedValues[0] <= sortedValues[1] &&
    exists k: nat :: k > 0 && isFibonacci(k) && isFibonacci(k+1) &&
        sortedValues[0] * getFibonacci(k+1) == sortedValues[1] * getFibonacci(k)
}

function isFibonacci(n: nat): bool
{
    n <= 100
}

function getFibonacci(n: nat): nat
{
    if n == 0 then 0
    else if n == 1 then 1
    else getFibonacci(n-1) + getFibonacci(n-2)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidResult(result)
    ensures result == GameResult(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(stdin_input);
    if |lines| >= 1 {
        var n := parseInt(lines[0]);
        if n == 3 && |lines| >= 2 {
            var values := parseInts(lines[1]);
            if |values| == 3 {
                var xorResult := xorSequence(values);
                if xorResult == 0 {
                    result := "BitAryo";
                } else {
                    result := "BitLGM";
                }
            } else {
                result := "BitLGM";
            }
        } else if n == 2 && |lines| >= 2 {
            var values := parseInts(lines[1]);
            if |values| == 2 && values[0] >= 0 && values[1] >= 0 {
                var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
                if goldenRatioRelation(sortedValues) {
                    result := "BitAryo";
                } else {
                    result := "BitLGM";
                }
            } else {
                result := "BitLGM";
            }
        } else if |lines| >= 2 {
            var value := parseInt(lines[1]);
            if value == 0 {
                result := "BitAryo";
            } else {
                result := "BitLGM";
            }
        } else {
            result := "BitLGM";
        }
    } else {
        result := "BitLGM";
    }
}
// </vc-code>

