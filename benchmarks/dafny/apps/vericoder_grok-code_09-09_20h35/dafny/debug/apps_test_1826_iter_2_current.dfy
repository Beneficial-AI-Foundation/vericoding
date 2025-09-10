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
function FindPos(s: seq<char>): int
    requires |s| > 0
    ensures 0 <= FindPos(s) <= |s|
    ensures FindPos(s) < |s| ==> s[FindPos(s)] == '\n'
{
    if s[0] == '\n' then 0 else if |s[1..]| > 0 then 1 + FindPos(s[1..]) else 1
}

function Minimize(s: seq<char>, res: seq<char>): seq<char>
    decreases |s|
{
    if |s| == 0 then res
    else if |res| > 0 && s[0] != res[0] then Minimize(s[1..], res[1..])
    else Minimize(s[1..], [s[0]] + res)
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
    var pos := FindPos(input);
    var sequence := input[..pos];
    var minimized := Minimize(sequence, []);
    result := minimized + "\n";
}
// </vc-code>

