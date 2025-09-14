function countNewlines(s: string): int
{
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + countNewlines(s[1..])
}

predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input && countNewlines(input) >= 3
}

function extractAndNormalizePuzzle1(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 2 then
        var line1 := lines[0];
        var line2 := reverse(lines[1]);
        var combined := line1 + line2;
        removeFirstX(combined)
    else
        ""
}

function extractAndNormalizePuzzle2(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 4 then
        var line3 := lines[2];
        var line4 := reverse(lines[3]);
        var combined := line3 + line4;
        removeFirstX(combined)
    else
        ""
}

predicate CanReachSameConfig(input: string)
    requires ValidInput(input)
{
    exists rotation :: 0 <= rotation < 4 && 
        extractAndNormalizePuzzle1(input) == rotatePuzzleLeft(extractAndNormalizePuzzle2(input), rotation)
}

// <vc-helpers>
function splitLines(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var t := splitLines(s[1..]);
        if s[0] == '\n' then [""] + t
        else if t == [] then [s[0..1]]
        else [s[0..1] + t[0]] + t[1..]
}

function reverse(s: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else reverse(s[1..]) + s[0..1]
}

function removeFirstX(s: string): string
{
    if |s| > 0 && s[0] == 'X' then s[1..]
    else s
}

function rotatePuzzleLeft(s: string, rotation: int): string
    requires 0 <= rotation < 4
{
    var n := |s|;
    if n == 0 then ""
    else
        var r := rotation % n;
        s[r..] + s[0..r]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> CanReachSameConfig(input)
// </vc-spec>
// <vc-code>
{
    var puzzle1 := extractAndNormalizePuzzle1(input);
    var puzzle2 := extractAndNormalizePuzzle2(input);
    if puzzle1 == rotatePuzzleLeft(puzzle2, 0) ||
       puzzle1 == rotatePuzzleLeft(puzzle2, 1) ||
       puzzle1 == rotatePuzzleLeft(puzzle2, 2) ||
       puzzle1 == rotatePuzzleLeft(puzzle2, 3) {
        return "YES\n";
    } else {
        return "NO\n";
    }
}
// </vc-code>

