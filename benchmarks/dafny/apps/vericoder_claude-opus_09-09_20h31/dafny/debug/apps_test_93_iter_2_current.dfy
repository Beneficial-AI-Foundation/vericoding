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
    ensures |splitLines(s)| >= countNewlines(s) + 1
{
    splitLinesHelper(s, "", [])
}

function splitLinesHelper(s: string, current: string, acc: seq<string>): seq<string>
    decreases |s|
    ensures |splitLinesHelper(s, current, acc)| == |acc| + countNewlines(s) + 1
{
    if |s| == 0 then
        acc + [current]
    else if s[0] == '\n' then
        splitLinesHelper(s[1..], "", acc + [current])
    else
        splitLinesHelper(s[1..], current + [s[0]], acc)
}

function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

function removeFirstX(s: string): string
{
    if |s| == 0 then ""
    else if s[0] == 'X' then s[1..]
    else s
}

function rotatePuzzleLeft(s: string, n: nat): string
    decreases n
{
    if n == 0 || |s| == 0 then s
    else rotatePuzzleLeft(rotateOnce(s), n - 1)
}

function rotateOnce(s: string): string
{
    if |s| <= 1 then s
    else s[1..] + [s[0]]
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
    
    var found := false;
    var rotation := 0;
    
    while rotation < 4
        invariant 0 <= rotation <= 4
        invariant found ==> exists r :: 0 <= r < rotation && puzzle1 == rotatePuzzleLeft(puzzle2, r)
        invariant !found ==> forall r :: 0 <= r < rotation ==> puzzle1 != rotatePuzzleLeft(puzzle2, r)
    {
        if puzzle1 == rotatePuzzleLeft(puzzle2, rotation) {
            found := true;
            break;
        }
        rotation := rotation + 1;
    }
    
    if found {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

