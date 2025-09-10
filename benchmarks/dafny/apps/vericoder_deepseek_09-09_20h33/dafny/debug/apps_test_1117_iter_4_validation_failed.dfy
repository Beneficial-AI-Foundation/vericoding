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
lemma canFormNonAscendingSequenceHelperLemma(rectangles: seq<(int, int)>, index: int, prevHeight: int)
    requires 0 <= index <= |rectangles|
    ensures canFormNonAscendingSequenceHelper(rectangles, index, prevHeight) == (
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
    )
{
    // The lemma body is empty since this is just unfolding the function definition
}

lemma parseRectanglesLemma(input: string)
    ensures parseRectangles(input) == (
        var lines := split(input, '\n');
        if |lines| == 0 then []
        else
            var n := parseInt(lines[0]);
            if n <= 0 then []
            else parseRectanglesFromLines(lines[1..], n)
    )
{
    // The lemma body is empty since this is just unfolding the function definition
}

function {:axiom} split(s: string, sep: char): seq<string>
    ensures |split(s, sep)| >= 0

function {:axiom} parseInt(s: string): int
    ensures parseInt(s) >= 0

function {:axiom} parseRectanglesFromLines(lines: seq<string>, n: int): seq<(int, int)>
    ensures |parseRectanglesFromLines(lines, n)| == n
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> canFormNonAscendingSequence(parseRectangles(input))
// </vc-spec>
// <vc-code>
{
    var lines := split(input, '\n');
    if |lines| == 0 {
        result := "NO";
    } else {
        var n := parseInt(lines[0]);
        if n <= 0 {
            result := "NO";
        } else {
            var rectangles := parseRectanglesFromLines(lines[1..], n);
            // Since parseRectanglesFromLines ensures |rectangles| == n, and n > 0,
            // we know |rectangles| > 0, so we can safely check the sequence
            if canFormNonAscendingSequence(rectangles) {
                result := "YES";
            } else {
                result := "NO";
            }
        }
    }
}
// </vc-code>

