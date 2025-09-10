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
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + splitLines(s[1..])
    else 
        var rest := splitLines(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
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

function rotatePuzzleLeft(puzzle: string, times: int): string
    requires 0 <= times < 4
{
    if times == 0 then puzzle
    else if times == 1 then rotateLeft(puzzle)
    else if times == 2 then rotateLeft(rotateLeft(puzzle))
    else rotateLeft(rotateLeft(rotateLeft(puzzle)))
}

function rotateLeft(puzzle: string): string
{
    puzzle
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
    
    while rotation < 4 && !found
        invariant 0 <= rotation <= 4
        invariant found ==> exists r :: 0 <= r < rotation && puzzle1 == rotatePuzzleLeft(puzzle2, r)
        invariant !found ==> forall r :: 0 <= r < rotation ==> puzzle1 != rotatePuzzleLeft(puzzle2, r)
    {
        if puzzle1 == rotatePuzzleLeft(puzzle2, rotation) {
            found := true;
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

