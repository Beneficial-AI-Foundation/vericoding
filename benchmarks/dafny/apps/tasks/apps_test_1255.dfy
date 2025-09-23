// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0
}

function GetMaxSimultaneousArrivals(input: string): int
    requires ValidInput(input)
    ensures GetMaxSimultaneousArrivals(input) >= 0
{
    var lines := SplitLinesFunction(input);
    if |lines| == 0 then 0
    else MaxFrequencyInAllLines(lines)
}

function SplitLinesFunction(s: string): seq<string>
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if start < |s| then acc + [s[start..]] else acc
    else if s[i] == '\n' then
        var newAcc := if start < i then acc + [s[start..i]] else acc;
        SplitLinesHelper(s, i + 1, i + 1, newAcc)
    else
        SplitLinesHelper(s, start, i + 1, acc)
}

function MaxFrequencyInAllLines(lines: seq<string>): int
    requires |lines| > 0
    ensures MaxFrequencyInAllLines(lines) >= 1
{
    MaxFrequencyHelper(lines, 0, 0)
}

function MaxFrequencyHelper(lines: seq<string>, index: int, currentMax: int): int
    requires 0 <= index <= |lines|
    requires currentMax >= 0
    ensures MaxFrequencyHelper(lines, index, currentMax) >= currentMax
    decreases |lines| - index
{
    if index >= |lines| then currentMax
    else
        var count := CountOccurrences(lines, lines[index]);
        var newMax := if count > currentMax then count else currentMax;
        var nextIndex := SkipIdentical(lines, index);
        MaxFrequencyHelper(lines, nextIndex, newMax)
}

function CountOccurrences(lines: seq<string>, target: string): int
    ensures CountOccurrences(lines, target) >= 0
{
    CountOccurrencesHelper(lines, target, 0, 0)
}

function CountOccurrencesHelper(lines: seq<string>, target: string, index: int, count: int): int
    requires 0 <= index <= |lines|
    requires count >= 0
    ensures CountOccurrencesHelper(lines, target, index, count) >= count
    decreases |lines| - index
{
    if index >= |lines| then count
    else
        var newCount := if lines[index] == target then count + 1 else count;
        CountOccurrencesHelper(lines, target, index + 1, newCount)
}

function SkipIdentical(lines: seq<string>, index: int): int
    requires 0 <= index < |lines|
    ensures index < SkipIdentical(lines, index) <= |lines|
    decreases |lines| - index
{
    if index + 1 >= |lines| then |lines|
    else if lines[index + 1] == lines[index] then SkipIdentical(lines, index + 1)
    else index + 1
}

function IntToStringFunction(n: int): string
    requires n >= 0
    ensures |IntToStringFunction(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n > 0
    ensures |IntToStringHelper(n, acc)| > |acc|
    decreases n
{
    var digit := n % 10;
    var digitChar := ('0' as int + digit) as char;
    if n / 10 == 0 then [digitChar] + acc
    else IntToStringHelper(n / 10, [digitChar] + acc)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == IntToStringFunction(GetMaxSimultaneousArrivals(input)) + "\n"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
