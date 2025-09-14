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

// <vc-helpers>
function CharToString(n: nat): (s: string)
    requires 0 <= n < 10
    ensures |s| == 1
{
    if n == 0 then "0" else
    if n == 1 then "1" else
    if n == 2 then "2" else
    if n == 3 then "3" else
    if n == 4 then "4" else
    if n == 5 then "5" else
    if n == 6 then "6" else
    if n == 7 then "7" else
    if n == 8 then "8" else
    "9"
}

function IntToString(n: nat): (s: string)
    ensures |s| > 0
{
    if n < 10 then
        CharToString(n)
    else
        IntToString(n / 10) + CharToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    var pos := 0;
    while pos < |input| && input[pos] != '\n'
        invariant 0 <= pos <= |input|
        invariant forall j :: 0 <= j < pos ==> input[j] != '\n'
    {
        pos := pos + 1;
    }
    
    var length := pos;
    var s := input[0..length];
    
    var replacements := CountReplacements(s, 0, length);
    var minimized_length := MinimizedLength(length, replacements);
    var result_num_str := IntToString(minimized_length);
    result := result_num_str + "\n";
}
// </vc-code>

