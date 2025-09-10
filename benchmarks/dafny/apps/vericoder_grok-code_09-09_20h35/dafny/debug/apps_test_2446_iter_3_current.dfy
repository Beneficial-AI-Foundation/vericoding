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
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
  if b == 0 then a
  else gcd(b, a % b)
}

function SplitLinesHelper(s: string, i: nat, current: string, lines: seq<string>): seq<string>
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then
    if current != "" then lines + [current] else lines
  else if s[i] == '\n' then
    SplitLinesHelper(s, i + 1, "", if current != "" then lines + [current] else lines)
  else
    SplitLinesHelper(s, i + 1, current + [s[i]], lines)
}

function ParseIntHelper(s: string, i: nat, value: int): int
  requires i >= 0 && i <= |s|
  requires 0 <= value
  requires forall k :: 0 <= k < |s| && (s[k] != ' ' && s[k] != '\n') ==> s[k] in "0123456789"
  decreases |s| - i
{
  if i == |s| then value
  else if s[i] in "0123456789" then ParseIntHelper(s, i + 1, value * 10 + (s[i] as int - '0' as int))
  else value
}

function ParseIntArrayHelper(s: string, i: nat, current: string, array: seq<int>): seq<int>
  decreases |s| - i
{
  if i == |s| then
    if current != "" then array + [ParseIntHelper(current, 0, 0)] else array
  else if s[i] == ' ' then
    if current != "" then ParseIntArrayHelper(s, i + 1, "", array + [ParseIntHelper(current, 0, 0)])
    else ParseIntArrayHelper(s, i + 1, "", array)
  else
    ParseIntArrayHelper(s, i + 1, current + [s[i]], array)
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then if acc == "" then "0" else acc
  else IntToStringHelper(n / 10, (n % 10 + '0' as int) as string + acc)
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
  var n := ParseIntFunc(lines[0]);
  var arr := ParseIntArrayFunc(lines[1]);
  var q := ParseIntFunc(lines[2]);
  var results: seq<int> := [];
  for i := 0 to q - 1 
  {
    var target := ParseIntFunc(lines[3 + i]);
    var count := CountSubarraysWithGCD(arr, target);
    results := results + [count];
  }
  result := FormatOutput(results);
}
// </vc-code>

