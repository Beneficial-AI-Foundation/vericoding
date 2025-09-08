Given a sequence of moves 'U' (up) and 'R' (right), replace consecutive pairs "RU" or "UR" 
with diagonal moves "D" to minimize sequence length. Input format is a number n followed by 
newline, then a string of n characters containing only 'U' and 'R'.

predicate ValidInput(input: string)
{
    |input| > 0 && exists pos :: 0 <= pos < |input| && input[pos] == '\n'
}

predicate ValidMoveSequence(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
}

function CountReplacements(s: string, start: int, length: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    ensures CountReplacements(s, start, length) >= 0
    ensures CountReplacements(s, start, length) <= length / 2
{
    if length <= 1 then 0
    else CountReplacementsHelper(s, start, length, 1, 0)
}

function CountReplacementsHelper(s: string, start: int, length: int, i: int, count: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    requires 1 <= i <= length
    requires count >= 0
    requires count <= (i - 1) / 2
    ensures CountReplacementsHelper(s, start, length, i, count) >= count
    ensures CountReplacementsHelper(s, start, length, i, count) <= length / 2
    decreases length - i
{
    if i >= length then count
    else if start + i < |s| && s[start + i - 1] != s[start + i] then
        if i + 2 <= length then CountReplacementsHelper(s, start, length, i + 2, count + 1)
        else count + 1
    else
        CountReplacementsHelper(s, start, length, i + 1, count)
}

function MinimizedLength(originalLength: int, replacements: int): int
    requires originalLength >= 0
    requires replacements >= 0
    requires replacements <= originalLength / 2
{
    originalLength - replacements
}

function ParseInteger(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    ParseIntegerHelper(s, 0, 0)
}

function ParseIntegerHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires acc >= 0
    ensures ParseIntegerHelper(s, pos, acc) >= 0
    decreases |s| - pos
{
    if pos >= |s| then acc
    else ParseIntegerHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 1
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    ensures |IntToStringHelper(n, acc)| >= |acc|
    ensures n == 0 ==> IntToStringHelper(n, acc) == acc
    ensures n > 0 || |acc| >= 1 ==> |IntToStringHelper(n, acc)| >= 1
    decreases n
{
    if n == 0 then acc
    else IntToStringHelper(n / 10, [((n % 10) as char + '0' as char)] + acc)
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
{
    // Find the newline to separate n from the string
    var newlinePos := 0;
    while newlinePos < |input| && input[newlinePos] != '\n'
        invariant 0 <= newlinePos <= |input|
        invariant forall k :: 0 <= k < newlinePos ==> input[k] != '\n'
    {
        newlinePos := newlinePos + 1;
    }

    // Parse n
    var n := 0;
    var i := 0;
    while i < newlinePos && i < |input|
        invariant 0 <= i <= newlinePos
        invariant 0 <= i <= |input|
        invariant n >= 0
    {
        if '0' <= input[i] <= '9' {
            n := n * 10 + (input[i] as int - '0' as int);
        }
        i := i + 1;
    }

    // Get the string part (skip the newline)
    var stStart := newlinePos + 1;

    var ans := n;
    if n > 1 && stStart < |input| && stStart + n <= |input| {
        var replacements := CountReplacements(input, stStart, n);
        ans := MinimizedLength(n, replacements);
    }

    result := IntToString(ans) + "\n";
}
