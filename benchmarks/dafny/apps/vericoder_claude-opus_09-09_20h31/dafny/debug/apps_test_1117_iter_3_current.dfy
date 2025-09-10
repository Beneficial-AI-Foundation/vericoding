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
function split(s: string, delim: char): seq<string>
{
    splitHelper(s, delim, [], "")
}

function splitHelper(s: string, delim: char, acc: seq<string>, current: string): seq<string>
    decreases |s|
{
    if |s| == 0 then 
        if |current| == 0 then acc else acc + [current]
    else if s[0] == delim then
        if |current| == 0 then splitHelper(s[1..], delim, acc, "")
        else splitHelper(s[1..], delim, acc + [current], "")
    else 
        splitHelper(s[1..], delim, acc, current + [s[0]])
}

function parseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -(parseNat(s[1..]) as int)
    else parseNat(s) as int
}

function parseNat(s: string): nat
{
    if |s| == 0 then 0
    else if '0' <= s[0] <= '9' then
        (s[0] as int - '0' as int) * pow10(|s| - 1) + parseNat(s[1..])
    else 0
}

function pow10(n: nat): nat
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

function parseRectanglesFromLines(lines: seq<string>, n: int): seq<(int, int)>
    decreases n
{
    if n <= 0 || |lines| == 0 then []
    else if |lines| < n then []
    else 
        var parts := split(lines[0], ' ');
        if |parts| < 2 then []
        else
            var a := parseInt(parts[0]);
            var b := parseInt(parts[1]);
            [(a, b)] + parseRectanglesFromLines(lines[1..], n - 1)
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

