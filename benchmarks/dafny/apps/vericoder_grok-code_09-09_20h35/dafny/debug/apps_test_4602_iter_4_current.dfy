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
predicate IsValidXArray(s: string, n: int, k: int) {
 var parts := SplitBySpace(s);
 |parts| == n &&
 forall i :: 0 <= i < |parts| ==> IsNonNegativeInteger(parts[i]) &&
 var num := StringToInt(parts[i]); num > 0 && num < k
}

function Min(a: int, b: int): int {
 if a <= b then a else b
}

function Sum(s: seq<int>): int
 requires forall i :: 0 <= i < |s| ==> s[i] >= 0
 decreases |s|
{
 if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

function IndexOf(s: string, c: char): int
 decreases |s|
{
 if |s| == 0 then -1
 else if s[0] == c then 0
 else
  var rest := IndexOf(s[1..], c);
  if rest == -1 then -1 else 1 + rest
}

function Split(s: string, sep: char): seq<string>
 decreases |s|
{
 if |s| == 0 then []
 else
  var pos := IndexOf(s, sep);
  if pos == -1 then [s]
  else [s[0..pos]] + Split(s[pos+1..], sep)
}

function SplitByNewlines(s: string): seq<string>
{
 Split(s, '\n')
}

function StringToInt(s: string): int
 requires IsNonNegativeInteger(s)
 decreases |s|
 ensures StringToInt(s) >= 0
{
 var val := (s[|s|-1] - '0') as int;
 if |s| == 1 then val
 else 10 * StringToInt(s[..|s|-1]) + val
}

function Map<T (!new), U>(s: seq<T>, f: T -> U): seq<U>
 decreases |s|
{
 if |s| == 0 then [] else [f(s[0])] + Map(s[1..], f)
}

function SplitBySpace(s: string): seq<string>
{
 Split(s, ' ')
}

function ParseIntArray(s: string): seq<int>
 requires forall part :: part in SplitBySpace(s) ==> IsNonNegativeInteger(part)
{
 var parts := SplitBySpace(s);
 Map(parts, x => StringToInt(x))
}

function IntToString(n: int): string
 requires n >= 0
 decreases n
 ensures IsNonNegativeInteger(IntToString(n))
 ensures StringToInt(IntToString(n)) == n
{
 if n == 0 then "0"
 else
  var tail := IntToString(n / 10);
  var digit := n % 10;
  tail + [(('0' as int + digit) as char)]
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
var expectedSum := ComputeMinDistance(x, k);
var resultStr := IntToString(expectedSum);
result := resultStr + "\n";
}
// </vc-code>

