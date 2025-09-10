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
function split(s: string, delimiter: char): seq<string>

function parseInt(s: string): int

function parseRectanglesFromLines(lines: seq<string>, n: int): seq<(int, int)>
    requires n >= 0
    decreases n
{
    if n == 0 || |lines| == 0 then []
    else if |lines| == 1 then
        if n == 1 then
            var parts := split(lines[0], ' ');
            if |parts| >= 2 then
                [(parseInt(parts[0]), parseInt(parts[1]))]
            else []
        else []
    else
        var parts := split(lines[0], ' ');
        if |parts| >= 2 then
            var rect := (parseInt(parts[0]), parseInt(parts[1]));
            [rect] + parseRectanglesFromLines(lines[1..], n - 1)
        else
            parseRectanglesFromLines(lines[1..], n - 1)
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
    var rectangles := parseRectangles(input);
    var canForm := canFormNonAscendingSequence(rectangles);
    
    if canForm {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

