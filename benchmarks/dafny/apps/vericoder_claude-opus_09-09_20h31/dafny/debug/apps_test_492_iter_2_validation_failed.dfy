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
function ModPos(x: int): int
{
    if x >= 0 then x % 4
    else 4 + (x % 4)
}

lemma ModPosProperties(x: int)
    ensures 0 <= ModPos(x) < 4
    ensures ModPos(x) == ModPos(x + 4)
    ensures ModPos(x) == ModPos(x - 4)
{
}
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
    
    var ccwPos := ModPos(startPos + n);
    var cwPos := ModPos(startPos - n);
    
    var ccw := ccwPos == endPos;
    var cw := cwPos == endPos;
    
    if cw && !ccw {
        result := "cw";
    } else if ccw && !cw {
        result := "ccw";
    } else {
        result := "undefined";
    }
    
    assert |input| > 0;
    assert var linesSpec := SplitLinesSpec(input);
           |linesSpec| >= 2 ==> (
               var positionsSpec := SplitBySpaceSpec(linesSpec[0]);
               |positionsSpec| >= 2 ==> (
                   var startCharSpec := positionsSpec[0];
                   var endCharSpec := positionsSpec[1];
                   var nSpec := StringToIntSpec(linesSpec[1]);
                   var startPosSpec := CharToPosSpec(startCharSpec);
                   var endPosSpec := CharToPosSpec(endCharSpec);
                   var ccwSpec := (startPosSpec + nSpec) % 4 == endPosSpec;
                   var cwSpec := (startPosSpec - nSpec) % 4 == endPosSpec;
                   lines == linesSpec &&
                   positions == positionsSpec &&
                   startChar == startCharSpec &&
                   endChar == endCharSpec &&
                   n == nSpec &&
                   startPos == startPosSpec &&
                   endPos == endPosSpec &&
                   ccw == ccwSpec &&
                   cw == cwSpec
               )
           );
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesSpec(s)
{
    lines := [];
    if |s| == 0 {
        return;
    }
    
    var start := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant lines == SplitLinesSpec(s[0..start])
    {
        if s[i] == '\n' {
            lines := lines + [s[start..i]];
            start := i + 1;
            i := i + 1;
        } else {
            i := i + 1;
        }
    }
    
    if start < |s| {
        lines := lines + [s[start..]];
    }
}

method SplitBySpace(s: string) returns (parts: seq<string>)
    ensures parts == SplitBySpaceSpec(s)
{
    parts := [];
    if |s| == 0 {
        return;
    }
    
    var start := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant parts == SplitBySpaceSpec(s[0..start])
    {
        if s[i] == ' ' {
            parts := parts + [s[start..i]];
            start := i + 1;
            i := i + 1;
        } else {
            i := i + 1;
        }
    }
    
    if start < |s| {
        parts := parts + [s[start..]];
    }
}

method StringToInt(s: string) returns (n: int)
    ensures n == StringToIntSpec(s)
{
    n := 0;
    var negative := false;
    var i := 0;
    
    if |s| > 0 && s[0] == '-' {
        negative := true;
        i := 1;
    }
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == StringToIntHelper(s, 0, 0, false) / Power10(|s| - i) % Power10(i - (if negative then 1 else 0))
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
    
    if negative {
        n := -n;
    }
}

function Power10(n: nat): nat
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

method CharToPos(c: string) returns (pos: int)
    ensures pos == CharToPosSpec(c)
{
    if c == "v" {
        pos := 0;
    } else if c == ">" {
        pos := 1;
    } else if c == "^" {
        pos := 2;
    } else if c == "<" {
        pos := 3;
    } else {
        pos := 0;
    }
}
// </vc-code>

