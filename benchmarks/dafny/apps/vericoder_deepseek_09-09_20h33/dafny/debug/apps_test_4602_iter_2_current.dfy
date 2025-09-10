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
function Sum(seq: seq<int>): (s: int)
    decreases seq
{
    if |seq| == 0 then 0
    else seq[0] + Sum(seq[1..])
}

lemma SumProps(seq: seq<int>)
    ensures Sum(seq) >= 0
    ensures forall i :: 0 <= i < |seq| ==> Sum(seq) >= seq[i]
{
}

function Min(a: int, b: int): int
{
    if a < b then a else b
}

function seq<T>(n: nat, f: int --> T): seq<T>
    ensures |result| == n
    ensures forall i :: 0 <= i < n ==> result[i] == f(i)
{
    if n == 0 then []
    else [f(0)] + seq(n-1, i => f(i+1))
}

predicate IsNonNegativeInteger(s: string) 
    ensures IsNonNegativeInteger(s) ==> |s| > 0
    ensures IsNonNegativeInteger(s) ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsPositiveInteger(s: string) 
    ensures IsPositiveInteger(s) ==> IsNonNegativeInteger(s)
    ensures IsPositiveInteger(s) ==> StringToInt(s) > 0
{
    IsNonNegativeInteger(s) && StringToInt(s) > 0 && (|s| == 1 || s[0] != '0')
}

predicate IsValidXArray(s: string, n: int, k: int)
    ensures IsValidXArray(s, n, k) ==> var x := ParseIntArray(s); |x| == n && forall i :: 0 <= i < n ==> 0 < x[i] < k
{
    var x := ParseIntArray(s);
    |x| == n && forall i :: 0 <= i < n ==> 0 < x[i] < k
}

function SplitByNewlines(s: string): seq<string>
    ensures |result| >= 0
    ensures |result| == 0 || (forall i :: 0 <= i < |result| ==> |result[i]| > 0)
{
    if |s| == 0 then []
    else var firstLine := ...;
         var rest := ...;
         [firstLine] + SplitByNewlines(rest)
}

function StringToInt(s: string): int
    requires IsNonNegativeInteger(s)
    ensures result >= 0
{
    if |s| == 0 then 0
    else (s[0] as int - '0' as int) * ... + StringToInt(s[1..])
}

function ParseIntArray(s: string): seq<int>
    requires |s| > 0
    ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
{
    var parts := SplitByWhitespace(s);
    seq(|parts|, i requires 0 <= i < |parts| => StringToInt(parts[i]))
}

function SplitByWhitespace(s: string): seq<string>
    ensures |result| >= 0
{
    ... // implementation depends on string splitting logic
}

ghost function ComputeMinDistance(x: seq<int>, k: int): int
    requires forall i :: 0 <= i < |x| ==> 0 < x[i] < k
    ensures result >= 0
{
    Sum(seq(|x|, i requires 0 <= i < |x| => 2 * Min(k - x[i], x[i])))
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
    
    var sum := 0;
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant sum == Sum(seq(i, j => 2 * Min(k - x[j], x[j])))
        invariant sum >= 0
    {
        var dist := 2 * Min(k - x[i], x[i]);
        sum := sum + dist;
        i := i + 1;
    }
    
    result := IntToString(sum) + "\n";
}
// </vc-code>

