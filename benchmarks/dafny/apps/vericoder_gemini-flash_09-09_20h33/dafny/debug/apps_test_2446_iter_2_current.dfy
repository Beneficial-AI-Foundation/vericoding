predicate ValidInput(input: string)
{
  var lines := SplitLinesFunc(input);
  |lines| >= 3 &&
  ParseIntFunc(lines[0]) > 0 &&
  ParseIntFunc(lines[2]) >= 0 &&
  |lines| >= 3 + ParseIntFunc(lines[2]) &&
  |ParseIntArrayFunc(lines[1])| == ParseIntFunc(lines[0]) &&
  (forall i {:trigger ParseIntArrayFunc(lines[1])[i]} :: 0 <= i < |ParseIntArrayFunc(lines[1])| ==> ParseIntArrayFunc(lines[1])[i] > 0) &&
  forall i {:trigger ParseIntFunc(lines[3 + i])} :: 0 <= i < ParseIntFunc(lines[2]) ==> ParseIntFunc(lines[3 + i]) > 0
}

function GetExpectedResults(input: string): seq<int>
  requires ValidInput(input)
  ensures forall x :: x in GetExpectedResults(input) ==> x >= 0
{
  var lines := SplitLinesFunc(input);
  var arr := ParseIntArrayFunc(lines[1]);
  var q := ParseIntFunc(lines[2]);
  seq(q, i requires 0 <= i < q => CountSubarraysWithGCD(arr, ParseIntFunc(lines[3 + i])))
}

function FormatOutput(results: seq<int>): string
  requires forall x :: x in results ==> x >= 0
  ensures forall x :: x in results ==> x >= 0 ==> IntToStringFunc(x) == IntToStringFunc(x)
{
  if |results| == 0 then ""
  else if |results| == 1 then (
    assert results[0] in results;
    IntToStringFunc(results[0])
  )
  else (
    assert results[0] in results;
    assert forall x :: x in results[1..] ==> x in results;
    IntToStringFunc(results[0]) + "\n" + FormatOutput(results[1..])
  )
}

function CountSubarraysWithGCD(arr: seq<int>, target: int): int
  requires |arr| > 0
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  requires target > 0
  ensures CountSubarraysWithGCD(arr, target) >= 0
{
  |set pair | pair in SubarrayPairs(arr) && SubarrayGCD(arr, pair.0, pair.1) == target|
}

function SubarrayPairs(arr: seq<int>): set<(int, int)>
  requires |arr| > 0
{
  set i, j | 0 <= i <= j < |arr| :: (i, j)
}

function SubarrayGCD(arr: seq<int>, start: int, end: int): int
  requires 0 <= start <= end < |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  ensures SubarrayGCD(arr, start, end) > 0
  decreases end - start
{
  if start == end then arr[start]
  else 
    var rest := SubarrayGCD(arr, start + 1, end);
    assert arr[start] > 0 && rest > 0;
    gcd(arr[start], rest)
}

function SplitLinesFunc(s: string): seq<string>
  ensures forall line :: line in SplitLinesFunc(s) ==> '\n' !in line
{
  SplitLinesHelper(s, 0, "", [])
}

function ParseIntFunc(s: string): int
  ensures ParseIntFunc(s) >= 0
{
  ParseIntHelper(s, 0, 0)
}

function ParseIntArrayFunc(s: string): seq<int>
  ensures forall x :: x in ParseIntArrayFunc(s) ==> x >= 0
{
  ParseIntArrayHelper(s, 0, "", [])
}

function IntToStringFunc(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else IntToStringHelper(n, "")
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0
  requires b > 0
  ensures gcd(a, b) > 0
  decreases a, b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function SplitLinesHelper(s: string, index: int, currentLine: string, acc: seq<string>): seq<string>
  ensures forall line :: line in SplitLinesHelper(s, index, currentLine, acc) ==> '\n' !in line
  decreases |s| - index
{
  if index == |s| then
    if |currentLine| > 0 then acc + [currentLine] else acc
  else if s[index] == '\n' then
    SplitLinesHelper(s, index + 1, "", acc + [currentLine])
  else
    SplitLinesHelper(s, index + 1, currentLine + s[index], acc)
}

function ParseIntHelper(s: string, index: int, value: int): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires value >= 0
  requires index >= 0
  decreases |s| - index
{
  if index == |s| then value
  else
    var digit := (s[index] as int) - ('0' as int);
    ParseIntHelper(s, index + 1, value * 10 + digit)
}

function ParseIntArrayHelper(s: string, index: int, currentNumStr: string, acc: seq<int>): seq<int>
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || s[i] == ' '
  requires forall x :: x in acc ==> x >= 0
  decreases |s| - index
{
  if index == |s| then
    if |currentNumStr| > 0 then acc + [ParseIntFunc(currentNumStr)] else acc
  else if s[index] == ' ' then
    if |currentNumStr| > 0 then
        ParseIntArrayHelper(s, index + 1, "", acc + [ParseIntFunc(currentNumStr)])
    else
        ParseIntArrayHelper(s, index + 1, "", acc)
  else
    ParseIntArrayHelper(s, index + 1, currentNumStr + s[index], acc)
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else
    var digit := n % 10;
    IntToStringHelper(n / 10, ((digit as char) + ('0' as int) as string) + acc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  requires ValidInput(input)
  ensures result == FormatOutput(GetExpectedResults(input))
// </vc-spec>
// <vc-code>
{
  var lines := SplitLinesFunc(input);
  var arr := ParseIntArrayFunc(lines[1]);
  var q := ParseIntFunc(lines[2]);
  var results := new int[q];

  var i := 0;
  while i < q
    invariant 0 <= i <= q
    invariant |lines| >= 3 + i
    invariant ParseIntFunc(lines[3 + i]) > 0
    invariant forall k :: 0 <= k < i ==> results[k] == CountSubarraysWithGCD(arr, ParseIntFunc(lines[3 + k]))
  {
    var target := ParseIntFunc(lines[3 + i]);
    var count := CountSubarraysWithGCD(arr, target);
    results[i] := count;
    i := i + 1;
  }
  result := FormatOutput(results);
}
// </vc-code>

