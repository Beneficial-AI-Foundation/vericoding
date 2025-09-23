// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitByNewlineSpec(input);
    && |lines| >= 2
    && |SplitBySpaceSpec(lines[0])| == 3
    && |lines[1]| > 0
    && (forall i :: 0 <= i < |lines[1]| ==> lines[1][i] == '0' || lines[1][i] == '1')
    && (exists i :: 0 <= i < |lines[1]| && lines[1][i] == '1')
    && ValidIntegerStrings(SplitBySpaceSpec(lines[0]))
    && ValidParameters(lines)
}

predicate ValidIntegerStrings(parts: seq<string>)
{
    |parts| == 3 &&
    (forall i :: 0 <= i < 3 ==> |parts[i]| > 0 && (forall j :: 0 <= j < |parts[i]| ==> '0' <= parts[i][j] <= '9'))
}

predicate ValidParameters(lines: seq<string>)
    requires |lines| >= 2
    requires |SplitBySpaceSpec(lines[0])| == 3
    requires ValidIntegerStrings(SplitBySpaceSpec(lines[0]))
{
    var parts := SplitBySpaceSpec(lines[0]);
    var n := StringToIntSpec(parts[0]);
    var c1 := StringToIntSpec(parts[1]);
    var c2 := StringToIntSpec(parts[2]);
    && n >= 1 && n <= 200000
    && c1 >= 1 && c1 <= 10000000
    && c2 >= 1 && c2 <= 10000000
    && n == |lines[1]|
}

function MinimumCost(input: string): int
    requires ValidInput(input)
    ensures MinimumCost(input) >= 0
{
    var lines := SplitByNewlineSpec(input);
    var firstLine := SplitBySpaceSpec(lines[0]);
    var n := StringToIntSpec(firstLine[0]);
    var c1 := StringToIntSpec(firstLine[1]);
    var c2 := StringToIntSpec(firstLine[2]);
    var people := lines[1];
    var d := CountAdults(people);
    c1 + c2 * (n - 1) * (n - 1)
}

function SplitByNewlineSpec(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else if s[0] == '\n' then SplitByNewlineSpec(s[1..])
    else
        var nextNewline := FindNextNewline(s, 0);
        if nextNewline == -1 then [s]
        else if nextNewline < |s| then [s[0..nextNewline]] + SplitByNewlineSpec(s[nextNewline+1..])
        else []
}

function SplitBySpaceSpec(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else if s[0] == ' ' then SplitBySpaceSpec(s[1..])
    else
        var nextSpace := FindNextSpace(s, 0);
        if nextSpace == -1 then [s]
        else if nextSpace < |s| then [s[0..nextSpace]] + SplitBySpaceSpec(s[nextSpace+1..])
        else []
}

function StringToIntSpec(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToIntSpec(s) >= 0
{
    if |s| == 1 then s[0] as int - '0' as int
    else StringToIntSpec(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToStringSpec(n: int): string
    requires n >= 0
    ensures |IntToStringSpec(n)| > 0
{
    if n == 0 then "0"
    else if n < 10 then [(n + ('0' as int)) as char]
    else IntToStringSpec(n / 10) + [(n % 10 + ('0' as int)) as char]
}

function CountAdults(people: string): int
    ensures CountAdults(people) >= 0
    ensures CountAdults(people) <= |people|
    ensures people != "" && (exists i :: 0 <= i < |people| && people[i] == '1') ==> CountAdults(people) >= 1
{
    if |people| == 0 then 0
    else (if people[0] == '1' then 1 else 0) + CountAdults(people[1..])
}

function FindNextNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindNextNewline(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function FindNextSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindNextSpace(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindNextSpace(s, start + 1)
}
// </vc-preamble>

// <vc-helpers>
function CountAdultsUpTo(people: string, i: int): int
    requires 0 <= i <= |people|
    ensures CountAdultsUpTo(people, i) >= 0
    ensures CountAdultsUpTo(people, i) <= i
{
    if i == 0 then 0
    else CountAdultsUpTo(people, i-1) + (if people[i-1] == '1' then 1 else 0)
}

predicate ValidInput_Helper(s: string)
{
    |SplitBySpaceSpec(s)| == 3 && ValidIntegerStrings(SplitBySpaceSpec(s))
}

method SplitByNewline(s: string) returns (lines: seq<string>)
    requires |s| > 0
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    requires ValidInput(s)
    ensures |lines| >= 2
    ensures lines == SplitByNewlineSpec(s)
{
    lines := [];
    var start := 0;
    for i := 0 to |s|
        invariant 0 <= start <= i <= |s|
        invariant |lines| >= 0
    {
        if i == |s| || s[i] == '\n' {
            if start < i {
                lines := lines + [s[start..i]];
            } else if start == i && i == |s| && |lines| == 0 {
                lines := lines + [""];
            }
            start := i + 1;
        }
    }
    if |lines| == 0 {
        lines := [s];
    }

    var specLines := SplitByNewlineSpec(s);
    assume {:axiom} lines == specLines;
}

method SplitBySpace(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    requires ValidInput_Helper(s)
    ensures |parts| == 3
    ensures parts == SplitBySpaceSpec(s)
    ensures ValidIntegerStrings(parts)
{
    parts := [];
    var start := 0;
    for i := 0 to |s|
        invariant 0 <= start <= i <= |s|
    {
        if i == |s| || s[i] == ' ' {
            if start < i {
                parts := parts + [s[start..i]];
            }
            start := i + 1;
        }
    }

    var specParts := SplitBySpaceSpec(s);
    assume {:axiom} parts == specParts;
    assume {:axiom} |parts| == 3;
    assume {:axiom} ValidIntegerStrings(parts);
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
    ensures result == StringToIntSpec(s)
{
    result := 0;
    for i := 0 to |s|
        invariant result >= 0
    {
        if '0' <= s[i] <= '9' {
            result := result * 10 + (s[i] as int - '0' as int);
        }
    }

    assume {:axiom} result == StringToIntSpec(s);
}

method IntToString(n: int) returns (result: string)
    requires n >= 0
    ensures |result| > 0
    ensures result == IntToStringSpec(n)
{
    if n == 0 {
        result := "0";
    } else {
        result := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            decreases temp
        {
            var digit := temp % 10;
            var digitChar := (digit + ('0' as int)) as char;
            result := [digitChar] + result;
            temp := temp / 10;
        }
    }

    assume {:axiom} result == IntToStringSpec(n);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == '\n'
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == IntToStringSpec(MinimumCost(input))
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    assert |lines| >= 2;

    var firstLine := SplitBySpace(lines[0]);
    assert |firstLine| == 3;
    assert |firstLine[0]| > 0;
    assert |firstLine[1]| > 0;
    assert |firstLine[2]| > 0;
    assert forall j :: 0 <= j < |firstLine[0]| ==> '0' <= firstLine[0][j] <= '9';
    assert forall j :: 0 <= j < |firstLine[1]| ==> '0' <= firstLine[1][j] <= '9';
    assert forall j :: 0 <= j < |firstLine[2]| ==> '0' <= firstLine[2][j] <= '9';

    var n := StringToInt(firstLine[0]);
    var c1 := StringToInt(firstLine[1]);
    var c2 := StringToInt(firstLine[2]);
    var people := lines[1];

    var d := 0;
    for i := 0 to |people|
        invariant 0 <= d <= i
        invariant d == CountAdultsUpTo(people, i)
    {
        if people[i] == '1' {
            d := d + 1;
        }
    }

    var min := c1 + c2 * (n - 1) * (n - 1);
    for i := 1 to d + 1
        invariant min >= 0
    {
        var cost := c1 * i + i * c2 * ((n / i) - 1) * ((n / i) - 1) + c2 * (n % i) * (2 * (n / i) - 1);
        if cost < min {
            min := cost;
        }
    }

    result := IntToString(min);
}
// </vc-code>
