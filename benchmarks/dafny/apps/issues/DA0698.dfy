// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 &&
    var lines := SplitLinesFunc(input);
    |lines| >= 1 && 
    IsValidNumber(lines[0]) &&
    var n := ParseIntFunc(lines[0]);
    1 <= n <= 5 &&
    |lines| == n + 1 &&
    (forall i :: 1 <= i <= n ==> |lines[i]| > 0 && IsValidRectangleLine(lines[i]))
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && (forall c :: c in s ==> '0' <= c <= '9')
}

predicate IsValidRectangleLine(s: string)
    requires |s| > 0
{
    var coords := ParseIntsFunc(s);
    |coords| == 4 &&
    coords[0] < coords[2] &&
    coords[1] < coords[3] &&
    0 <= coords[0] && coords[2] <= 31400 &&
    0 <= coords[1] && coords[3] <= 31400
}

predicate RectanglesFormSquare(input: string)
    requires ValidInput(input)
{
    var lines := SplitLinesFunc(input);
    var n := ParseIntFunc(lines[0]);

    var coords_seq := seq(n, i requires 0 <= i < n => ParseIntsFunc(lines[i+1]));
    var totalArea := SumAreas(coords_seq);
    var bounds := ComputeBounds(coords_seq);

    var width := bounds.1 - bounds.0;
    var height := bounds.3 - bounds.2;

    width == height && totalArea == width * width
}

function SumAreas(coords: seq<seq<int>>): int
    requires forall i :: 0 <= i < |coords| ==> |coords[i]| == 4
{
    if |coords| == 0 then 0
    else Abs(coords[0][2] - coords[0][0]) * Abs(coords[0][3] - coords[0][1]) + SumAreas(coords[1..])
}

function ComputeBounds(coords: seq<seq<int>>): (int, int, int, int)
    requires |coords| > 0
    requires forall i :: 0 <= i < |coords| ==> |coords[i]| == 4
{
    if |coords| == 1 then 
        (Min(coords[0][0], coords[0][2]), Max(coords[0][0], coords[0][2]), 
         Min(coords[0][1], coords[0][3]), Max(coords[0][1], coords[0][3]))
    else
        var restBounds := ComputeBounds(coords[1..]);
        var currMinX := Min(coords[0][0], coords[0][2]);
        var currMaxX := Max(coords[0][0], coords[0][2]);
        var currMinY := Min(coords[0][1], coords[0][3]);
        var currMaxY := Max(coords[0][1], coords[0][3]);
        (Min(currMinX, restBounds.0), Max(currMaxX, restBounds.1),
         Min(currMinY, restBounds.2), Max(currMaxY, restBounds.3))
}

function SplitLinesFunc(s: string): seq<string>
    requires |s| > 0
{
    SplitLinesHelper(s, 0, "", [])
}

function SplitLinesHelper(s: string, i: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 then lines + [current] else lines
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, "", lines + [current])
    else
        SplitLinesHelper(s, i + 1, current + [s[i]], lines)
}

function ParseIntFunc(s: string): int
    requires |s| > 0
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelper(s, i + 1, acc)
}

function ParseIntsFunc(s: string): seq<int>
    requires |s| > 0
{
    ParseIntsHelper(s, 0, "", [])
}

function ParseIntsHelper(s: string, i: int, current: string, nums: seq<int>): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 then nums + [ParseIntFunc(current)] else nums
    else if s[i] == ' ' then
        if |current| > 0 then
            ParseIntsHelper(s, i + 1, "", nums + [ParseIntFunc(current)])
        else
            ParseIntsHelper(s, i + 1, "", nums)
    else
        ParseIntsHelper(s, i + 1, current + [s[i]], nums)
}

function Abs(x: int): int
{
    if x >= 0 then x else -x
}

function Min(a: int, b: int): int
{
    if a < b then a else b
}

function Max(a: int, b: int): int
{
    if a > b then a else b
}
// </vc-preamble>

// <vc-helpers>
method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| > 0
    ensures lines == SplitLinesFunc(s)
{
    lines := [];
    var current := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant SplitLinesHelper(s, 0, "", []) == SplitLinesHelper(s, i, current, lines)
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        lines := lines + [current];
    }
}

method ParseInt(s: string) returns (result: int)
    requires |s| > 0
    ensures result == ParseIntFunc(s)
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
        invariant ParseIntHelper(s, 0, 0) == ParseIntHelper(s, i, result)
    {
        if '0' <= s[i] <= '9' {
            result := result * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
}

method ParseInts(s: string) returns (result: seq<int>)
    requires |s| > 0
    ensures result == ParseIntsFunc(s)
{
    result := [];
    var current := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ParseIntsHelper(s, 0, "", []) == ParseIntsHelper(s, i, current, result)
    {
        if s[i] == ' ' {
            if |current| > 0 {
                var num := ParseInt(current);
                result := result + [num];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        var num := ParseInt(current);
        result := result + [num];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> RectanglesFormSquare(input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var n := ParseInt(lines[0]);

    var s := 0;
    var INF := 1000000000;
    var minx := INF;
    var miny := INF;
    var maxx := -INF;
    var maxy := -INF;

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant i == 0 ==> (minx == INF && maxx == -INF && miny == INF && maxy == -INF && s == 0)
        invariant i > 0 ==> (minx < INF && maxx > -INF && miny < INF && maxy > -INF)
        invariant i > 0 ==> s == SumAreas(seq(i, j requires 0 <= j < i => ParseIntsFunc(lines[j+1])))
        invariant i > 0 ==> (minx, maxx, miny, maxy) == ComputeBounds(seq(i, j requires 0 <= j < i => ParseIntsFunc(lines[j+1])))
    {
        var tmpCall1 := ParseInts(lines[i+1]);
        var coords := tmpCall1;
        var x1 := coords[0];
        var y1 := coords[1];
        var x2 := coords[2];
        var y2 := coords[3];

        s := s + Abs(x2 - x1) * Abs(y2 - y1);
        minx := Min(minx, Min(x1, x2));
        maxx := Max(maxx, Max(x1, x2));
        miny := Min(miny, Min(y1, y2));
        maxy := Max(maxy, Max(y1, y2));

        i := i + 1;
    }

    if (maxx - minx) == (maxy - miny) && s == (maxx - minx) * (maxx - minx) {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
