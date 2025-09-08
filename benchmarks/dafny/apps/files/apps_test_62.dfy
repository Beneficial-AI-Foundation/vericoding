Two players play a game on a sequence of n non-negative integers. Each player can either
reduce a single element by some value or globally reduce all elements by the minimum value.
The player who cannot make a move (all elements are 0) loses. Determine the winner assuming
both players play optimally.

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

function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + splitLines(s[1..])
    else
        var rest := splitLines(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function parseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -parseNat(s[1..])
    else parseNat(s)
}

function parseNat(s: string): int
{
    if |s| == 0 then 0
    else if s[0] < '0' || s[0] > '9' then 0
    else (s[0] as int - '0' as int) + 10 * parseNat(s[1..])
}

function parseInts(s: string): seq<int>
{
    var tokens := splitBySpace(s);
    seq(|tokens|, i requires 0 <= i < |tokens| => parseInt(tokens[i]))
}

function splitBySpace(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else if s[0] == ' ' then splitBySpace(s[1..])
    else
        var nextSpace := findSpace(s, 0);
        if nextSpace == |s| then [s]
        else if nextSpace < |s| then [s[0..nextSpace]] + splitBySpace(s[nextSpace+1..])
        else [s]
}

function findSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= findSpace(s, start) <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] == ' ' then start
    else findSpace(s, start + 1)
}

function xorSequence(values: seq<int>): int
{
    if |values| == 0 then 0
    else integerXor(values[0], xorSequence(values[1..]))
}

function goldenRatioRelation(values: seq<int>): bool
    requires |values| == 2
    requires forall i :: 0 <= i < |values| ==> values[i] >= 0
{
    var a := values[0];
    var b := values[1];
    a < 785 && b < 785 && phiLookupTable(a) == b
}

function phiLookupTable(index: int): int
    requires index >= 0 && index < 785
{
    if index < 300 then
        var phiIndex := (index * 1618) / 1000;
        var phi2Index := (index * 2618) / 1000;
        if phi2Index < 785 then phi2Index else 0
    else if index < 785 then
        var i := 0;
        phiLookupHelper(index, i)
    else 0
}

function phiLookupHelper(target: int, i: int): int
    requires target >= 0 && target < 785
    requires i >= 0
    decreases 300 - i
{
    if i >= 300 then 0
    else
        var phi2Index := (i * 2618) / 1000;
        if phi2Index == target then
            var phiIndex := (i * 1618) / 1000;
            if phiIndex < 785 then phiIndex else 0
        else phiLookupHelper(target, i + 1)
}

function integerXor(a: int, b: int): int
{
    if a == 0 then b
    else if b == 0 then a
    else if a < 0 && b >= 0 then -integerXorPositive(-a, b)
    else if a >= 0 && b < 0 then -integerXorPositive(a, -b)
    else if a < 0 && b < 0 then integerXorPositive(-a, -b)
    else integerXorPositive(a, b)
}

function integerXorPositive(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else
        var aBit := a % 2;
        var bBit := b % 2;
        var resultBit := if aBit == bBit then 0 else 1;
        resultBit + 2 * integerXorPositive(a / 2, b / 2)
}

method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidResult(result)
    ensures result == GameResult(stdin_input)
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
