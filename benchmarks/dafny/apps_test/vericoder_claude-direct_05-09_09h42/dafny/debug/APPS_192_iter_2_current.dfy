// ======= TASK =======
// Given an equilateral triangle with integer side length x, find the minimum number of operations 
// to transform it into an equilateral triangle with integer side length y, where y < x.
// In each operation, you can change the length of exactly one side, maintaining triangle inequality
// and positive integer constraints.

// ======= SPEC REQUIREMENTS =======
function ValidInput(x: int, y: int): bool
{
    3 <= y < x <= 100000
}

function ComputeMinOperations(x: int, y: int): int
requires ValidInput(x, y)
{
    ComputeMinOperationsHelper(x, x, x, 0, y)
}

function ComputeMinOperationsHelper(A: int, B: int, curr: int, count: int, y: int): int
requires curr >= 3 && y <= 100000
requires A <= B && curr == B
requires A >= 3
decreases if curr <= y then y - curr else 0
{
    if curr >= y then count + 2
    else
        var newCurr := B + A - 1;
        if newCurr <= y then
            ComputeMinOperationsHelper(B, newCurr, newCurr, count + 1, y)
        else
            count + 2
}

function SplitByNewlineSpec(s: string): seq<string>
{
    SplitByNewlineImpl(s, 0, "", [])
}

function SplitByNewlineImpl(s: string, i: int, current: string, acc: seq<string>): seq<string>
requires 0 <= i <= |s|
decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then acc + [current] else acc
    else if s[i] == '\n' then
        SplitByNewlineImpl(s, i + 1, "", acc + [current])
    else
        SplitByNewlineImpl(s, i + 1, current + [s[i]], acc)
}

function SplitBySpaceSpec(s: string): seq<string>
{
    SplitBySpaceImpl(s, 0, "", [])
}

function SplitBySpaceImpl(s: string, i: int, current: string, acc: seq<string>): seq<string>
requires 0 <= i <= |s|
decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then acc + [current] else acc
    else if s[i] == ' ' then
        if |current| > 0 then
            SplitBySpaceImpl(s, i + 1, "", acc + [current])
        else
            SplitBySpaceImpl(s, i + 1, "", acc)
    else
        SplitBySpaceImpl(s, i + 1, current + [s[i]], acc)
}

function parseIntSpec(s: string): int
{
    parseIntImpl(s, 0, 0, false)
}

function parseIntImpl(s: string, i: int, acc: int, negative: bool): int
requires 0 <= i <= |s|
decreases |s| - i
{
    if i >= |s| then
        if negative then -acc else acc
    else if i == 0 && s[i] == '-' then
        parseIntImpl(s, i + 1, acc, true)
    else if '0' <= s[i] <= '9' then
        parseIntImpl(s, i + 1, acc * 10 + (s[i] as int - '0' as int), negative)
    else
        parseIntImpl(s, i + 1, acc, negative)
}

function IntToStringSpec(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringPositive(-n)
    else IntToStringPositive(n)
}

function IntToStringPositive(n: int): string
requires n > 0
decreases n
{
    if n < 10 then
        [(n + '0' as int) as char]
    else
        IntToStringPositive(n / 10) + [(n % 10 + '0' as int) as char]
}

// <vc-helpers>
method computeOperations(x: int, y: int) returns (result: int)
requires ValidInput(x, y)
ensures result >= 2
ensures result == ComputeMinOperations(x, y)
{
    var A := x;
    var B := x;
    var curr := x;
    var count := 0;

    while curr < y
    decreases y - curr
    invariant curr >= x
    invariant A >= x && B >= x
    invariant count >= 0
    invariant curr == B
    invariant A <= B
    invariant curr < y ==> B + A - 1 > curr
    invariant ComputeMinOperations(x, y) == ComputeMinOperationsHelper(A, B, curr, count, y)
    {
        var newCurr := B + A - 1;
        if newCurr > y {
            result := count + 2;
            return;
        }
        A := B;
        B := newCurr;
        curr := newCurr;
        count := count + 1;
    }

    result := count + 2;
}

method SplitByNewline(s: string) returns (lines: seq<string>)
requires |s| >= 0
ensures |lines| >= 0
ensures lines == SplitByNewlineSpec(s)
{
    lines := SplitByNewlineImpl(s, 0, "", []);
}

method SplitBySpace(s: string) returns (parts: seq<string>)
requires |s| >= 0
ensures |parts| >= 0
ensures parts == SplitBySpaceSpec(s)
{
    parts := SplitBySpaceImpl(s, 0, "", []);
}

method parseInt(s: string) returns (result: int)
requires |s| >= 0
ensures result == parseIntSpec(s)
{
    result := parseIntImpl(s, 0, 0, false);
}

method IntToString(n: int) returns (s: string)
ensures |s| >= 1
ensures s == IntToStringSpec(n)
{
    s := IntToStringSpec(n);
}

lemma ValidInputSwap(x: int, y: int)
requires ValidInput(x, y)
ensures ValidInput(y, x)
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
requires |input| > 0
requires exists lines :: lines == SplitByNewlineSpec(input) && |lines| >= 1
requires exists parts :: parts == SplitBySpaceSpec(SplitByNewlineSpec(input)[0]) && |parts| >= 2
requires exists x, y :: x == parseIntSpec(SplitBySpaceSpec(SplitByNewlineSpec(input)[0])[0]) && 
                       y == parseIntSpec(SplitBySpaceSpec(SplitByNewlineSpec(input)[0])[1]) &&
                       ValidInput(y, x)
ensures |output| >= 1
ensures exists x_parsed, y_parsed :: x_parsed == parseIntSpec(SplitBySpaceSpec(SplitByNewlineSpec(input)[0])[0]) && 
                                    y_parsed == parseIntSpec(SplitBySpaceSpec(SplitByNewlineSpec(input)[0])[1]) &&
                                    ValidInput(y_parsed, x_parsed) && output == IntToStringSpec(ComputeMinOperations(y_parsed, x_parsed))
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    var parts := SplitBySpace(lines[0]);
    
    var x_parsed := parseInt(parts[0]);
    var y_parsed := parseInt(parts[1]);
    
    ValidInputSwap(y_parsed, x_parsed);
    
    var result := computeOperations(y_parsed, x_parsed);
    output := IntToString(result);
}
// </vc-code>

