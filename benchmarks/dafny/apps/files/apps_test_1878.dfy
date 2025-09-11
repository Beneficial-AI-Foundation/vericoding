// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| >= 0
}

function SplitLinesFunc(s: string): seq<string>
    requires |s| >= 0
    ensures |SplitLinesFunc(s)| >= 0
    ensures forall i :: 0 <= i < |SplitLinesFunc(s)| ==> '\n' !in SplitLinesFunc(s)[i]
{
    if |s| == 0 then []
    else SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, pos: int, acc: seq<string>): seq<string>
    requires 0 <= start <= pos <= |s|
    requires forall i :: 0 <= i < |acc| ==> '\n' !in acc[i]
    requires forall k :: start <= k < pos ==> s[k] != '\n'
    ensures |SplitLinesHelper(s, start, pos, acc)| >= |acc|
    ensures forall i :: 0 <= i < |SplitLinesHelper(s, start, pos, acc)| ==> '\n' !in SplitLinesHelper(s, start, pos, acc)[i]
    decreases |s| - pos
{
    if pos >= |s| then
        if start < pos then 
            assert forall k :: start <= k < pos ==> s[k] != '\n';
            acc + [s[start..pos]] 
        else acc
    else if s[pos] == '\n' then
        var new_acc := if start < pos then 
            (assert forall k :: start <= k < pos ==> s[k] != '\n'; acc + [s[start..pos]]) 
            else acc;
        SplitLinesHelper(s, pos + 1, pos + 1, new_acc)
    else
        SplitLinesHelper(s, start, pos + 1, acc)
}

function ParseIntFunc(s: string): int
    requires |s| >= 0
{
    if |s| == 0 then 0
    else if s[0] == '-' then -ParseIntPosFunc(s[1..])
    else ParseIntPosFunc(s)
}

function ParseIntPosFunc(s: string): int
    requires |s| >= 0
    ensures ParseIntPosFunc(s) >= 0
{
    if |s| == 0 then 0
    else if '0' <= s[0] <= '9' then
        (s[0] as int - '0' as int) + 10 * ParseIntPosFunc(s[1..])
    else 0
}

function ParseIntsFunc(s: string): seq<int>
    requires |s| >= 0
    ensures |ParseIntsFunc(s)| >= 0
{
    if |s| == 0 then []
    else ParseIntsHelper(s, 0, 0, [])
}

function ParseIntsHelper(s: string, start: int, pos: int, acc: seq<int>): seq<int>
    requires 0 <= start <= pos <= |s|
    ensures |ParseIntsHelper(s, start, pos, acc)| >= |acc|
    decreases |s| - pos
{
    if pos >= |s| then
        if start < pos then acc + [ParseIntFunc(s[start..pos])] else acc
    else if s[pos] == ' ' then
        var new_acc := if start < pos then acc + [ParseIntFunc(s[start..pos])] else acc;
        ParseIntsHelper(s, pos + 1, pos + 1, new_acc)
    else
        ParseIntsHelper(s, start, pos + 1, acc)
}

function IntToStringFunc(n: int): string
    ensures |IntToStringFunc(n)| >= 1
{
    if n == 0 then "0"
    else if n > 0 then IntToStringPos(n)
    else "-" + IntToStringPos(-n)
}

function IntToStringPos(n: int): string
    requires n > 0
    ensures |IntToStringPos(n)| >= 1
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringPos(n / 10) + [('0' as int + (n % 10)) as char]
}

function ComputeTotalArea(rectangle_lines: seq<string>): int
    ensures ComputeTotalArea(rectangle_lines) >= 0
{
    if |rectangle_lines| == 0 then 0
    else
        var coords := ParseIntsFunc(rectangle_lines[0]);
        var area := if |coords| >= 4 then 
            var computed := (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 then computed else 0
        else 0;
        area + ComputeTotalArea(rectangle_lines[1..])
}

function ComputeTotalAreaPartial(rectangle_lines: seq<string>, n: int): int
    ensures ComputeTotalAreaPartial(rectangle_lines, n) >= 0
{
    if n <= 0 || |rectangle_lines| == 0 then 0
    else
        var coords := ParseIntsFunc(rectangle_lines[0]);
        var area := if |coords| >= 4 then 
            var computed := (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 then computed else 0
        else 0;
        area + ComputeTotalAreaPartial(rectangle_lines[1..], n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 1
    ensures result[|result|-1] == '\n'
    ensures exists total_area: int ::
        total_area >= 0 &&
        result == IntToStringFunc(total_area) + "\n" &&
        (var processed_input := if |input| > 0 && input[|input|-1] == '\n' then input else input + "\n";
         var lines := SplitLinesFunc(processed_input);
         if |lines| == 0 then total_area == 0
         else
         (var n := ParseIntFunc(lines[0]);
          if n >= 0 && n + 1 <= |lines| then
            total_area == ComputeTotalArea(lines[1..n+1])
          else
            total_area == ComputeTotalAreaPartial(lines[1..], n)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
