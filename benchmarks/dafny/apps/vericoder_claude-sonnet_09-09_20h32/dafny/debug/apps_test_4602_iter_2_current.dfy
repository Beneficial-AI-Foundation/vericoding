predicate ValidInput(s: string) {
    var lines := SplitByNewlines(s);
    |lines| >= 3 &&
    IsPositiveInteger(lines[0]) &&
    IsPositiveInteger(lines[1]) &&
    var n := StringToInt(lines[0]);
    var k := StringToInt(lines[1]);
    1 <= n <= 100 &&
    1 <= k <= 100 &&
    IsValidXArray(lines[2], n, k)
}

predicate ValidOutput(result: string) {
    |result| >= 2 &&
    result[|result|-1] == '\n' &&
    IsNonNegativeInteger(result[..|result|-1])
}

predicate CorrectSolution(input: string, output: string) {
    ValidInput(input) && ValidOutput(output) ==>
        var lines := SplitByNewlines(input);
        var n := StringToInt(lines[0]);
        var k := StringToInt(lines[1]);
        var x := ParseIntArray(lines[2]);
        |x| == n &&
        (forall i :: 0 <= i < n ==> 0 < x[i] < k) &&
        var expectedSum := ComputeMinDistance(x, k);
        StringToInt(output[..|output|-1]) == expectedSum
}

predicate IsPositiveInteger(s: string) {
    IsNonNegativeInteger(s) && |s| > 0 && (|s| > 1 || s[0] != '0') && StringToInt(s) > 0
}

predicate IsNonNegativeInteger(s: string) {
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidXArray(s: string, n: int, k: int) {
    var x := ParseIntArray(s);
    |x| == n && forall i :: 0 <= i < n ==> 0 < x[i] < k
}

function ComputeMinDistance(x: seq<int>, k: int): int
    requires forall i :: 0 <= i < |x| ==> 0 < x[i] < k
    ensures ComputeMinDistance(x, k) >= 0
{
    Sum(seq(|x|, i requires 0 <= i < |x| => 2 * Min(k - x[i], x[i])))
}

// <vc-helpers>
function SplitByNewlines(s: string): seq<string>
    ensures |SplitByNewlines(s)| >= 1
{
    SplitByNewlinesHelper(s, 0, "", [])
}

function SplitByNewlinesHelper(s: string, i: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |s|
    ensures |SplitByNewlinesHelper(s, i, current, lines)| >= 1
    decreases |s| - i
{
    if i == |s| then
        lines + [current]
    else if s[i] == '\n' then
        SplitByNewlinesHelper(s, i + 1, "", lines + [current])
    else
        SplitByNewlinesHelper(s, i + 1, current + [s[i]], lines)
}

function StringToInt(s: string): int
    requires IsNonNegativeInteger(s)
    ensures StringToInt(s) >= 0
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
    requires n >= 0
    ensures IsNonNegativeInteger(IntToString(n))
    ensures StringToInt(IntToString(n)) == n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + n % 10) as char]
}

function ParseIntArray(s: string): seq<int>
{
    ParseIntArrayHelper(s, 0, "", [])
}

function ParseIntArrayHelper(s: string, i: int, current: string, nums: seq<int>): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 && IsNonNegativeInteger(current) then
            nums + [StringToInt(current)]
        else
            nums
    else if s[i] == ' ' then
        if |current| > 0 && IsNonNegativeInteger(current) then
            ParseIntArrayHelper(s, i + 1, "", nums + [StringToInt(current)])
        else
            ParseIntArrayHelper(s, i + 1, "", nums)
    else
        ParseIntArrayHelper(s, i + 1, current + [s[i]], nums)
}

function Min(a: int, b: int): int
{
    if a <= b then a else b
}

function Sum(xs: seq<int>): int
{
    if |xs| == 0 then 0
    else xs[0] + Sum(xs[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires ValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures ValidOutput(result)
    ensures CorrectSolution(s, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewlines(s);
    var n := StringToInt(lines[0]);
    var k := StringToInt(lines[1]);
    var x := ParseIntArray(lines[2]);
    
    var totalDistance := ComputeMinDistance(x, k);
    result := IntToString(totalDistance) + "\n";
}
// </vc-code>

