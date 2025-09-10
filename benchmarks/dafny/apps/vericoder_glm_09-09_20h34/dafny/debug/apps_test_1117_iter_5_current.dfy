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
function split(s: string, sep: char): seq<string>
{
    if s == "" then [""]
    else splitHelper(s, sep, 0, [""])
}

function splitHelper(s: string, sep: char, i: int, tokens: seq<string>): seq<string>
    requires 0 <= i <= |s|
    requires tokens != []
    decreases |s| - i
{
    if i == |s| then tokens
    else if s[i] == sep then 
        splitHelper(s, sep, i+1, tokens + [""])
    else 
        var currentToken := tokens[|tokens|-1];
        var newToken := currentToken + s[i].ToString();
        var newTokens := tokens[0..|tokens|-1] + [newToken];
        splitHelper(s, sep, i+1, newTokens)
}

function parseInt(s: string): int
    requires forall i :: 0 <= i < |s| => '0' <= s[i] <= '9'
{
    parseIntHelper(s, 0, 0)
}

function parseIntHelper(s: string, i: int, num: int): int
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < i => '0' <= s[j] <= '9'
    decreases |s| - i
{
    if i == |s| then num
    else parseIntHelper(s, i+1, num * 10 + (s[i] - '0'))
}

function parseRectanglesFromLines(lines: seq<string>, n: int): seq<(int, int)>
    requires 0 <= n <= |lines|
{
    if n == 0 then []
    else
        var line := lines[0];
        var parts := split(line, ' ');
        var a := parseInt(parts[0]);
        var b := parseInt(parts[1]);
        var rect := (a, b);
        var rest := parseRectanglesFromLines(lines[1..], n-1);
        rect + rest
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
    if canFormNonAscendingSequence(rects) {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

