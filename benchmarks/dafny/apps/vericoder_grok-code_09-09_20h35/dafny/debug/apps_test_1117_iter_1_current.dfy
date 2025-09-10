function canFormNonAscendingSequence(rectangles: seq<(int, int)>): bool
{
    if |rectangles| <= 1 then true
    else canFormNonAscendingSequenceHelper(rectangles, 1, max(rectangles[0].0, rectangles[0].1))
}

function canFormNonAscendingSequenceHelper(rectangles: seq<(int, int)>, index: int, prevHeight: int): bool
    requires 0 <= index <= |rectangles|
    decreases |rectangles| - index
{
    if index >= |rectangles| then true
    else
        var a := rectangles[index].0;
        var b := rectangles[index].1;
        var minDim := min(a, b);
        var maxDim := max(a, b);

        if minDim > prevHeight then false
        else if minDim <= prevHeight < maxDim then 
            canFormNonAscendingSequenceHelper(rectangles, index + 1, minDim)
        else 
            canFormNonAscendingSequenceHelper(rectangles, index + 1, maxDim)
}

function parseRectangles(input: string): seq<(int, int)>
{
    var lines := split(input, '\n');
    if |lines| == 0 then []
    else
        var n := parseInt(lines[0]);
        if n <= 0 then []
        else parseRectanglesFromLines(lines[1..], n)
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}

// <vc-helpers>
function findFirstDelim(s: string, delim: char): int
    decreases |s|
{
    if |s| == 0 then 0
    else if s[0] == delim then 0
    else 1 + findFirstDelim(s[1..], delim)
}

function split(s: string, delim: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var idx := findFirstDelim(s, delim);
        if idx < |s| then [s[..idx]] + split(s[idx+1..], delim)
        else [s]
}

function parseInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 1 then s[0] - '0' as int
    else 10 * parseInt(s[..|s|-1]) + (s[|s|-1] - '0' as int)
}

function parseOneRectangle(line: string): (int,int)
    requires |line| > 0
    ensures var parts := split(line, ' '); |parts| >= 2 && 
           (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
           (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9')
{
    var parts := split(line, ' ');
    var a := parseInt(parts[0]);
    var b := parseInt(parts[1]);
    (a, b)
}

function parseRectanglesFromLines(lines: seq<string>, n: int): seq<(int,int)>
    requires |lines| == n
    decreases n
{
    if n == 0 then []
    else parseOneRectangle(lines[0]) + parseRectanglesFromLines(lines[1..], n-1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> canFormNonAscendingSequence(parseRectangles(input))
// </vc-spec>
// <vc-code>
{
    var rects := parseRectangles(input);
    var b := canFormNonAscendingSequence(rects);
    if b then result := "YES"; else result := "NO";
}
// </vc-code>

