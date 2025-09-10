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
{
    SplitByNewlinesHelper(s, 0, 0)
}

function SplitByNewlinesHelper(s: string, start: int, i: int): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then []
        else [s[start..i]]
    else if s[i] == '\n' then
        [s[start..i]] + SplitByNewlinesHelper(s, i+1, i+1)
    else
        SplitByNewlinesHelper(s, start, i+1)
}

function StringToInt(s: string): int
    requires IsNonNegativeInteger(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then (s[0] - '0') as int
    else StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as int
}

function ParseIntArray(s: string): seq<int>
{
    ParseIntArrayHelper(SplitBySpaces(s))
}

function SplitBySpaces(s: string): seq<string>
{
    SplitBySpacesHelper(s, 0, 0)
}

function SplitBySpacesHelper(s: string, start: int, i: int): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then []
        else [s[start..i]]
    else if s[i] == ' ' then
        if start == i then SplitBySpacesHelper(s, i+1, i+1)
        else [s[start..i]] + SplitBySpacesHelper(s, i+1, i+1)
    else
        SplitBySpacesHelper(s, start, i+1)
}

function ParseIntArrayHelper(parts: seq<string>): seq<int>
{
    if |parts| == 0 then []
    else if IsNonNegativeInteger(parts[0]) then
        [StringToInt(parts[0])] + ParseIntArrayHelper(parts[1..])
    else
        ParseIntArrayHelper(parts[1..])
}

function IntToString(n: int): string
    requires n >= 0
    ensures IsNonNegativeInteger(IntToString(n))
    ensures StringToInt(IntToString(n)) == n
{
    if n == 0 then "0"
    else if n < 10 then ['0' + n as char]
    else IntToString(n / 10) + ['0' + (n % 10) as char]
}

function Min(a: int, b: int): int
    ensures Min(a, b) <= a && Min(a, b) <= b
    ensures Min(a, b) == a || Min(a, b) == b
    ensures a >= 0 && b >= 0 ==> Min(a, b) >= 0
{
    if a <= b then a else b
}

function Sum(s: seq<int>): int
    ensures |s| == 0 ==> Sum(s) == 0
    ensures |s| > 0 ==> Sum(s) == s[0] + Sum(s[1..])
    ensures (forall i :: 0 <= i < |s| ==> s[i] >= 0) ==> Sum(s) >= 0
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

lemma SumPrefix(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < |s| ==> s[j] >= 0
    ensures Sum(s) >= Sum(s[..i])
{
    if i == 0 {
        assert s[..0] == [];
        assert Sum(s[..0]) == 0;
        SumNonNegative(s);
    } else if i == |s| {
        assert s[..i] == s;
    } else {
        if |s| > 0 {
            assert s[1..][..i-1] == s[..i][1..];
            SumPrefix(s[1..], i-1);
            assert Sum(s[1..]) >= Sum(s[1..][..i-1]);
            assert s[..i][0] == s[0];
            assert Sum(s[..i]) == s[0] + Sum(s[..i][1..]);
            assert Sum(s) == s[0] + Sum(s[1..]);
        }
    }
}

lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures Sum(s) >= 0
{
    if |s| == 0 {
    } else {
        SumNonNegative(s[1..]);
    }
}

lemma MinDistanceNonNegative(x: seq<int>, k: int)
    requires forall i :: 0 <= i < |x| ==> 0 < x[i] < k
    ensures forall i :: 0 <= i < |x| ==> 2 * Min(k - x[i], x[i]) >= 0
{
    forall i | 0 <= i < |x|
    ensures 2 * Min(k - x[i], x[i]) >= 0
    {
        assert x[i] > 0;
        assert k - x[i] > 0;
        assert Min(k - x[i], x[i]) >= 0;
    }
}

lemma ComputeMinDistanceIsNonNegative(x: seq<int>, k: int)
    requires forall i :: 0 <= i < |x| ==> 0 < x[i] < k
    ensures ComputeMinDistance(x, k) >= 0
{
    var distances := seq(|x|, i requires 0 <= i < |x| => 2 * Min(k - x[i], x[i]));
    MinDistanceNonNegative(x, k);
    assert forall i :: 0 <= i < |distances| ==> distances[i] >= 0;
    assert ComputeMinDistance(x, k) == Sum(distances);
    SumNonNegative(distances);
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
    
    var distances := seq(|x|, i requires 0 <= i < |x| => 2 * Min(k - x[i], x[i]));
    
    MinDistanceNonNegative(x, k);
    assert forall i :: 0 <= i < |distances| ==> distances[i] >= 0;
    
    var totalDistance := Sum(distances);
    
    SumNonNegative(distances);
    assert totalDistance >= 0;
    assert totalDistance == ComputeMinDistance(x, k);
    
    result := IntToString(totalDistance) + "\n";
}
// </vc-code>

