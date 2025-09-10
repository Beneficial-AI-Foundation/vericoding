function CharToPosSpec(c: string): int
{
    if c == "v" then 0
    else if c == ">" then 1
    else if c == "^" then 2
    else if c == "<" then 3
    else 0
}

function SplitLinesSpec(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := FindNewline(s, 0);
        if i == |s| then [s]
        else [s[0..i]] + SplitLinesSpec(s[i+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNewline(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function SplitBySpaceSpec(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := FindSpace(s, 0);
        if i == |s| then [s]
        else [s[0..i]] + SplitBySpaceSpec(s[i+1..])
}

function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindSpace(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function StringToIntSpec(s: string): int
{
    StringToIntHelper(s, 0, 0, false)
}

function StringToIntHelper(s: string, pos: int, acc: int, negative: bool): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then (if negative then -acc else acc)
    else if pos == 0 && s[pos] == '-' then StringToIntHelper(s, pos + 1, acc, true)
    else if '0' <= s[pos] <= '9' then 
        StringToIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int), negative)
    else StringToIntHelper(s, pos + 1, acc, negative)
}

predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(result: string)
{
    result == "cw" || result == "ccw" || result == "undefined"
}

// <vc-helpers>
function ModPos(a: int, b: int): int
    requires b > 0
    ensures 0 <= ModPos(a, b) < b
{
    if a >= 0 then a % b
    else ((a % b) + b) % b
}

lemma ModPosCorrect(a: int, b: int)
    requires b > 0
    ensures ModPos(a, b) == ((a % b) + b) % b
{}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures |input| > 0 ==> (
        var lines := SplitLinesSpec(input);
        |lines| >= 2 ==> (
            var positions := SplitBySpaceSpec(lines[0]);
            |positions| >= 2 ==> (
                var startChar := positions[0];
                var endChar := positions[1];
                var n := StringToIntSpec(lines[1]);
                var startPos := CharToPosSpec(startChar);
                var endPos := CharToPosSpec(endChar);
                var ccw := (startPos + n) % 4 == endPos;
                var cw := (startPos - n) % 4 == endPos;
                (cw && !ccw ==> result == "cw") &&
                (ccw && !cw ==> result == "ccw") &&
                (!(cw && !ccw) && !(ccw && !cw) ==> result == "undefined")
            )
        )
    )
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        return "undefined";
    }
    
    var positions := SplitBySpace(lines[0]);
    if |positions| < 2 {
        return "undefined";
    }
    
    var startChar := positions[0];
    var endChar := positions[1];
    var n := StringToInt(lines[1]);
    
    var startPos := CharToPos(startChar);
    var endPos := CharToPos(endChar);
    
    var ccwPos := ModPos(startPos + n, 4);
    var cwPos := ModPos(startPos - n, 4);
    
    var ccw := ccwPos == endPos;
    var cw := cwPos == endPos;
    
    if cw && !ccw {
        result := "cw";
    } else if ccw && !cw {
        result := "ccw";
    } else {
        result := "undefined";
    }
    
    assert ValidOutput(result);
}
// </vc-code>

