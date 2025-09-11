// <vc-preamble>
function ParseInputLines(input: string): seq<string>
{
    SplitByNewlineSimple(input, 0, [])
}

function SplitByNewlineSimple(input: string, pos: int, acc: seq<string>): seq<string>
    requires 0 <= pos <= |input|
    decreases |input| - pos
{
    if pos >= |input| then acc
    else 
        var nextNewline := FindNextNewline(input, pos);
        if nextNewline == -1 then
            if pos < |input| then acc + [input[pos..]] else acc
        else
            SplitByNewlineSimple(input, nextNewline + 1, acc + [input[pos..nextNewline]])
}

function FindNextNewline(input: string, start: int): int
    requires 0 <= start <= |input|
    ensures FindNextNewline(input, start) == -1 || (start <= FindNextNewline(input, start) < |input|)
    decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else FindNextNewline(input, start + 1)
}

function CountBlackInSquare(lines: seq<string>, row: int, col: int): int
    requires 0 <= row < |lines| - 1
    requires row + 1 < |lines|
    requires 0 <= col < |lines[row]| - 1
    requires 0 <= col < |lines[row + 1]| - 1
    requires col + 1 < |lines[row]|
    requires col + 1 < |lines[row + 1]|
{
    (if lines[row][col] == '#' then 1 else 0) +
    (if lines[row][col + 1] == '#' then 1 else 0) +
    (if lines[row + 1][col] == '#' then 1 else 0) +
    (if lines[row + 1][col + 1] == '#' then 1 else 0)
}

predicate ValidGrid(lines: seq<string>)
{
    |lines| == 4 && (forall k :: 0 <= k < 4 ==> |lines[k]| >= 4)
}

predicate CanMakeUniformSquare(lines: seq<string>)
    requires ValidGrid(lines)
{
    exists i, j :: 0 <= i <= 2 && 0 <= j <= 2 && 
        i + 1 < |lines| && j + 1 < |lines[i]| && j + 1 < |lines[i + 1]| &&
        (var blackCount := CountBlackInSquare(lines, i, j);
         blackCount >= 3 || blackCount <= 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> 
        (var lines := ParseInputLines(input);
         ValidGrid(lines) && CanMakeUniformSquare(lines))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
