// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitLinesSpec(input);
    |lines| >= 2 && |ParseIntegersSpec(lines[1])| > 0
}

function SplitLinesSpec(s: string): seq<string>
    ensures forall line :: line in SplitLinesSpec(s) ==> '\n' !in line
{
    SplitLinesHelper(s, 0)
}

function ParseIntegersSpec(line: string): seq<int>
    ensures forall n :: n in ParseIntegersSpec(line) ==> n >= 0
{
    ParseIntegersHelper(line, 0)
}

function MinDeclined(ranks: seq<int>): int
    requires |ranks| > 0
    ensures MinDeclined(ranks) >= 0
    ensures MinDeclined(ranks) == (if Maximum(ranks) > 25 then Maximum(ranks) - 25 else 0)
{
    var maxRank := Maximum(ranks);
    if maxRank > 25 then maxRank - 25 else 0
}
// </vc-preamble>

// <vc-helpers>
function SplitLinesHelper(s: string, start: int): seq<string>
    requires 0 <= start <= |s|
    ensures forall line :: line in SplitLinesHelper(s, start) ==> '\n' !in line
    decreases |s| - start
{
    if start >= |s| then
        if start == 0 then [] else [""]
    else
        var nextNewline := FindNextNewline(s, start);
        if nextNewline == -1 then
            [s[start..]]
        else
            [s[start..nextNewline]] + SplitLinesHelper(s, nextNewline + 1)
}

function FindNextNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures FindNextNewline(s, start) == -1 || (start <= FindNextNewline(s, start) < |s| && s[FindNextNewline(s, start)] == '\n')
    ensures FindNextNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
    ensures FindNextNewline(s, start) != -1 ==> forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function ParseIntegersHelper(line: string, pos: int): seq<int>
    requires 0 <= pos <= |line|
    ensures forall n :: n in ParseIntegersHelper(line, pos) ==> n >= 0
    decreases |line| - pos
{
    if pos >= |line| then []
    else if line[pos] == ' ' then ParseIntegersHelper(line, pos + 1)
    else if line[pos] !in "0123456789" then ParseIntegersHelper(line, pos + 1)
    else
        var endPos := FindEndOfNumber(line, pos);
        [ParseInt(line, pos, endPos)] + ParseIntegersHelper(line, endPos)
}

function FindEndOfNumber(line: string, start: int): int
    requires 0 <= start < |line|
    requires line[start] in "0123456789"
    ensures start < FindEndOfNumber(line, start) <= |line|
    ensures forall i :: start <= i < FindEndOfNumber(line, start) ==> line[i] in "0123456789"
    decreases |line| - start
{
    if start + 1 >= |line| || line[start + 1] !in "0123456789" then start + 1
    else FindEndOfNumber(line, start + 1)
}

function ParseInt(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] in "0123456789"
    requires start < end
    ensures ParseInt(s, start, end) >= 0
    decreases end - start
{
    if start + 1 == end then
        s[start] as int - '0' as int
    else
        ParseInt(s, start, end-1) * 10 + (s[end-1] as int - '0' as int)
}

function Maximum(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> Maximum(s) >= s[i]
    ensures Maximum(s) in s
{
    if |s| == 1 then s[0]
    else if s[0] >= Maximum(s[1..]) then s[0]
    else Maximum(s[1..])
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + n % 10) as char]
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures forall line :: line in lines ==> '\n' !in line
    ensures lines == SplitLinesSpec(s)
{
    lines := SplitLinesSpec(s);
}

method ParseIntegers(line: string) returns (nums: seq<int>)
    ensures forall n :: n in nums ==> n >= 0
    ensures nums == ParseIntegersSpec(line)
{
    nums := ParseIntegersSpec(line);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures var lines := SplitLinesSpec(input);
            if |lines| >= 2 then
                var ranks := ParseIntegersSpec(lines[1]);
                if |ranks| > 0 then
                    output == IntToString(MinDeclined(ranks)) + "\n"
                else
                    output == ""
            else
                output == ""
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        output := "";
        return;
    }

    var secondLine := lines[1];
    var ranks := ParseIntegers(secondLine);

    if |ranks| == 0 {
        output := "";
        return;
    }

    var result := MinDeclined(ranks);
    output := IntToString(result) + "\n";
}
// </vc-code>
