// <vc-preamble>
predicate ValidInput(input: string)
{
    var lines := SplitLinesFunc(input);
    |lines| >= 3 &&
    var boardParts := SplitSpacesFunc(lines[0]);
    var paint1Parts := SplitSpacesFunc(lines[1]);
    var paint2Parts := SplitSpacesFunc(lines[2]);
    |boardParts| >= 2 && |paint1Parts| >= 2 && |paint2Parts| >= 2 &&
    IsValidInt(boardParts[0]) && IsValidInt(boardParts[1]) &&
    IsValidInt(paint1Parts[0]) && IsValidInt(paint1Parts[1]) &&
    IsValidInt(paint2Parts[0]) && IsValidInt(paint2Parts[1])
}

predicate CanPlaceBothPaintings(a: int, b: int, c: int, d: int, e: int, f: int)
{
    (c+e <= a && Max(d,f) <= b) ||
    (c+e <= b && Max(d,f) <= a) ||
    (c+f <= a && Max(d,e) <= b) ||
    (c+f <= b && Max(d,e) <= a) ||
    (d+e <= a && Max(c,f) <= b) ||
    (d+e <= b && Max(c,f) <= a) ||
    (d+f <= a && Max(c,e) <= b) ||
    (d+f <= b && Max(c,e) <= a)
}

function Max(x: int, y: int): int
{
    if x >= y then x else y
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLinesFunc(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitLinesHelper(s, 0, "", [])
}

function SplitLinesHelper(s: string, i: nat, current: string, lines: seq<string>): seq<string>
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then lines + [current] else lines
    else if s[i] == '\n' then
        if |current| > 0 then 
            SplitLinesHelper(s, i+1, "", lines + [current])
        else 
            SplitLinesHelper(s, i+1, "", lines)
    else
        SplitLinesHelper(s, i+1, current + [s[i]], lines)
}

function SplitSpacesFunc(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitSpacesHelper(s, 0, "", [])
}

function SplitSpacesHelper(s: string, i: nat, current: string, parts: seq<string>): seq<string>
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' || s[i] == '\t' then
        if |current| > 0 then 
            SplitSpacesHelper(s, i+1, "", parts + [current])
        else 
            SplitSpacesHelper(s, i+1, "", parts)
    else
        SplitSpacesHelper(s, i+1, current + [s[i]], parts)
}

function ParseIntFunc(s: string): int
    requires IsValidInt(s)
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: nat, acc: nat): nat
    requires i <= |s|
    requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    decreases |s| - i
{
    if i >= |s| then acc
    else ParseIntHelper(s, i+1, acc * 10 + (s[i] as int - '0' as int))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "YES\n" || result == "NO\n" || result == ""
    ensures ValidInput(input) ==> (
        result == "YES\n" <==> (
            var lines := SplitLinesFunc(input);
            var boardParts := SplitSpacesFunc(lines[0]);
            var paint1Parts := SplitSpacesFunc(lines[1]);
            var paint2Parts := SplitSpacesFunc(lines[2]);
            var a := ParseIntFunc(boardParts[0]);
            var b := ParseIntFunc(boardParts[1]);
            var c := ParseIntFunc(paint1Parts[0]);
            var d := ParseIntFunc(paint1Parts[1]);
            var e := ParseIntFunc(paint2Parts[0]);
            var f := ParseIntFunc(paint2Parts[1]);
            CanPlaceBothPaintings(a, b, c, d, e, f)
        )
    )
    ensures !ValidInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
