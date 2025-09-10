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
    ensures |splitLines(s)| == countNewlines(s) + 1
    ensures forall i :: 0 <= i < |splitLines(s)| ==> (splitLines(s)[i] != "" || i == |splitLines(s)| - 1)
{
    if |s| == 0 then [""]
    else if s[0] == '\n' then [""] + splitLines(s[1..])
    else
        var restLines := splitLines(s[1..]);
        [s[0..1] + restLines[0]] + restLines[1..]
}

function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + s[0..1]
}

function removeFirstX(s: string): string
    requires |s| > 0
{
    s[1..]
}

function rotatePuzzleLeft(s: string, rotation: int): string
    requires 0 <= rotation < 4
    requires |s| > 0
{
    if rotation == 0 then s
    else rotatePuzzleLeft(s[1..] + s[0..1], rotation - 1)
}

predicate puzzleEqual(s1: string, s2: string)
{
    |s1| == |s2| && (s1 == s2 || (|s1| > 0 && puzzleEqual(s1[1..] + s[0..1], s2)))
}

lemma rotatePuzzleLeftLemma(s: string, rotation: int)
    requires 0 <= rotation < 4
    requires |s| > 0
    ensures puzzleEqual(rotatePuzzleLeft(s, rotation), s)
{
    if rotation > 0 {
        var rotated := s[1..] + s[0..1];
        rotatePuzzleLeftLemma(rotated, rotation - 1);
    }
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
    if |splitLines(input)| >= 4 {
        var puzzle1 := extractAndNormalizePuzzle1(input);
        var puzzle2 := extractAndNormalizePuzzle2(input);
        
        var found := false;
        var rotation := 0;
        while rotation < 4
            invariant 0 <= rotation <= 4
            invariant found == (exists r :: 0 <= r < rotation && puzzleEqual(puzzle1, rotatePuzzleLeft(puzzle2, r)))
        {
            if puzzleEqual(puzzle1, rotatePuzzleLeft(puzzle2, rotation)) {
                found := true;
            }
            rotation := rotation + 1;
        }
        
        if found {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    } else {
        result := "NO\n";
    }
}
// </vc-code>

