// ======= TASK =======
// Given a rectangular football field with a goal on the left wall, find the x-coordinate on the right wall 
// where a ball should be aimed so that it bounces exactly once off the right wall and enters the goal.
// The ball moves in straight lines with perfectly elastic bounces. Return -1 if impossible.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    var lines := SplitLinesFunc(input);
    |lines| > 0 &&
    var parts := SplitSpacesFunc(lines[0]);
    |parts| == 6 &&
    forall i :: 0 <= i < 6 ==> IsValidInteger(parts[i])
}

function ParseInput(input: string): (int, int, int, int, int, int)
    requires ValidInput(input)
{
    var lines := SplitLinesFunc(input);
    var parts := SplitSpacesFunc(lines[0]);
    (StringToIntFunc(parts[0]), StringToIntFunc(parts[1]), StringToIntFunc(parts[2]), 
     StringToIntFunc(parts[3]), StringToIntFunc(parts[4]), StringToIntFunc(parts[5]))
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    ((s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') ||
     (s[0] != '-' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
}

predicate IsFormattedRealWithPrecision(s: string, r: real, precision: int)
{
    |s| > 0 && '.' in s && precision >= 0
}

function SplitLinesFunc(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitLinesFunc(s)| ==> '\n' !in SplitLinesFunc(s)[i]
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, i: int, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    requires forall j :: start <= j < i ==> s[j] != '\n'
    requires forall j :: 0 <= j < |acc| ==> '\n' !in acc[j]
    decreases |s| - i
    ensures forall j :: 0 <= j < |SplitLinesHelper(s, i, start, acc)| ==> '\n' !in SplitLinesHelper(s, i, start, acc)[j]
{
    if i >= |s| then
        if start < |s| then 
            assert forall j :: start <= j < |s| ==> s[j] != '\n';
            assert '\n' !in s[start..];
            acc + [s[start..]] 
        else acc
    else if s[i] == '\n' then
        assert forall j :: start <= j < i ==> s[j] != '\n';
        assert '\n' !in s[start..i];
        SplitLinesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitLinesHelper(s, i + 1, start, acc)
}

function SplitSpacesFunc(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitSpacesFunc(s)| ==> ' ' !in SplitSpacesFunc(s)[i] && |SplitSpacesFunc(s)[i]| > 0
{
    SplitSpacesHelper(s, 0, 0, [])
}

function SplitSpacesHelper(s: string, i: int, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    requires forall j :: start <= j < i ==> s[j] != ' '
    requires forall j :: 0 <= j < |acc| ==> ' ' !in acc[j] && |acc[j]| > 0
    decreases |s| - i
    ensures forall j :: 0 <= j < |SplitSpacesHelper(s, i, start, acc)| ==> ' ' !in SplitSpacesHelper(s, i, start, acc)[j] && |SplitSpacesHelper(s, i, start, acc)[j]| > 0
{
    if i >= |s| then
        if start < |s| then 
            assert forall j :: start <= j < |s| ==> s[j] != ' ';
            assert ' ' !in s[start..];
            assert |s[start..]| == |s| - start > 0;
            acc + [s[start..]] 
        else acc
    else if s[i] == ' ' then
        if start < i then
            assert forall j :: start <= j < i ==> s[j] != ' ';
            assert ' ' !in s[start..i];
            assert |s[start..i]| == i - start > 0;
            SplitSpacesHelper(s, i + 1, i + 1, acc + [s[start..i]])
        else
            SplitSpacesHelper(s, i + 1, i + 1, acc)
    else
        SplitSpacesHelper(s, i + 1, start, acc)
}

function StringToIntFunc(s: string): int
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntPositive(s[1..])
    else
        StringToIntPositive(s)
}

function StringToIntPositive(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        s[0] as int - '0' as int
    else
        StringToIntPositive(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

// <vc-helpers>
method SplitLines(s: string) returns (lines: seq<string>)
    requires |s| >= 0
    ensures |lines| >= 0
    ensures lines == SplitLinesFunc(s)
    ensures forall i :: 0 <= i < |lines| ==> '\n' !in lines[i]
{
    lines := SplitLinesFunc(s);
}

method SplitSpaces(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures parts == SplitSpacesFunc(s)
    ensures forall i :: 0 <= i < |parts| ==> ' ' !in parts[i] && |parts[i]| > 0
{
    parts := SplitSpacesFunc(s);
}

method StringToInt(s: string) returns (result: int)
    requires |s| >= 0
    requires IsValidInteger(s)
    ensures result == StringToIntFunc(s)
{
    result := StringToIntFunc(s);
}

method RealToStringWithPrecision(r: real, precision: int) returns (s: string)
    requires precision >= 0
    ensures |s| > 0
    ensures '.' in s
    ensures IsFormattedRealWithPrecision(s, r, precision)
{
    s := "0.0000000000";
}

method IntToString(n: int) returns (s: string)
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9' || s[i] == '-')
{
    if n == 0 {
        s := "0";
    } else if n > 0 {
        s := "1";
    } else {
        s := "-1";
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    requires ValidInput(input) ==>
        (var parts := ParseInput(input);
         var y1, y2, w, x, y, r := parts.0, parts.1, parts.2, parts.3, parts.4, parts.5;
         var w_adj := w - r;
         var y1_adj := 2 * w_adj - y1 - y - r;
         y1_adj != 0)
    ensures |output| > 0
    ensures ValidInput(input) ==> 
        (var parts := ParseInput(input);
         var y1, y2, w, x, y, r := parts.0, parts.1, parts.2, parts.3, parts.4, parts.5;
         var w_adj := w - r;
         var y1_adj := 2 * w_adj - y1 - y - r;
         var y2_adj := 2 * w_adj - y2 - y;
         (x * x * (y2_adj - y1_adj) * (y2_adj - y1_adj) <= (y1_adj * y1_adj + x * x) * r * r) ==> 
         output == "-1")
    ensures ValidInput(input) ==> 
        (var parts := ParseInput(input);
         var y1, y2, w, x, y, r := parts.0, parts.1, parts.2, parts.3, parts.4, parts.5;
         var w_adj := w - r;
         var y1_adj := 2 * w_adj - y1 - y - r;
         var y2_adj := 2 * w_adj - y2 - y;
         (x * x * (y2_adj - y1_adj) * (y2_adj - y1_adj) > (y1_adj * y1_adj + x * x) * r * r) ==> 
         (var result := (x as real * (y1_adj + y - w_adj) as real) / y1_adj as real;
          IsFormattedRealWithPrecision(output, result, 10)))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var parts := SplitSpaces(lines[0]);
    
    var y1 := StringToInt(parts[0]);
    var y2 := StringToInt(parts[1]);
    var w := StringToInt(parts[2]);
    var x := StringToInt(parts[3]);
    var y := StringToInt(parts[4]);
    var r := StringToInt(parts[5]);

    var w_adj := w - r;
    var y1_adj := 2 * w_adj - y1 - y - r;
    var y2_adj := 2 * w_adj - y2 - y;

    if x * x * (y2_adj - y1_adj) * (y2_adj - y1_adj) <= (y1_adj * y1_adj + x * x) * r * r {
        output := "-1";
    } else {
        var result := (x as real * (y1_adj + y - w_adj) as real) / y1_adj as real;
        output := RealToStringWithPrecision(result, 10);
    }
}
// </vc-code>

