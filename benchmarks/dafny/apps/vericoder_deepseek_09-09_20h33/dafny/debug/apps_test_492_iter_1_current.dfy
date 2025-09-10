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
lemma ModLemma(a: int, b: int)
    requires b != 0
    ensures ((a % b) + b) % b == a % b
{
}

lemma ClockwiseEquivalence(startPos: int, n: int, endPos: int)
    ensures (startPos - n) % 4 == endPos % 4 <==> (startPos + (4 - n % 4)) % 4 == endPos % 4
{
    if n % 4 != 0 {
        ModLemma(startPos - n, 4);
        ModLemma(startPos + (4 - n % 4), 4);
    }
}

function CharToPosString(c: string): int
{
    if c == "v" then 0
    else if c == ">" then 1
    else if c == "^" then 2
    else if c == "<" then 3
    else 0
}

predicate ValidSingleCharacter(s: string)
{
    |s| == 1 && (s[0] == 'v' || s[0] == '>' || s[0] == '^' || s[0] == '<')
}

lemma ValidInputImpliesValidFirstLine(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLinesSpec(input);
            |lines| >= 1 ==> (
                var firstLine := lines[0];
                var positions := SplitBySpaceSpec(firstLine);
                |positions| >= 2 ==> (
                    ValidSingleCharacter(positions[0]) &&
                    ValidSingleCharacter(positions[1])
                )
            )
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
    var lines := SplitLinesSpec(input);
    if |lines| < 2 {
        result := "undefined";
    } else {
        var positions := SplitBySpaceSpec(lines[0]);
        if |positions| < 2 {
            result := "undefined";
        } else {
            var startChar := positions[0];
            var endChar := positions[1];
            var n_str := lines[1];
            var n := StringToIntSpec(n_str);
            var startPos := CharToPosSpec(startChar);
            var endPos := CharToPosSpec(endChar);
            
            var adjusted_n := n % 4;
            var ccw := (startPos + n) % 4 == endPos;
            var cw := (startPos - n + 400) % 4 == endPos; // +400 to handle negative modulo
            
            if cw && !ccw {
                result := "cw";
            } else if ccw && !cw {
                result := "ccw";
            } else {
                result := "undefined";
            }
        }
    }
}
// </vc-code>

