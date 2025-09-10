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
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  ensures forall d: int :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
  decreases b
{
  if b == 0 then a
  else gcd(b, a % b)
}

function SplitLinesHelper(s: string, index: int, current: string, acc: seq<string>): seq<string>
  ensures forall line :: line in SplitLinesHelper(s, index, current, acc) ==> '\n' !in line
  decreases |s| - index, |current|
{
  if index == |s| then
    if |current| > 0 then acc + [current] else acc
  else if s[index] == '\n' then
    SplitLinesHelper(s, index + 1, "", acc + [current])
  else
    SplitLinesHelper(s, index + 1, current + [s[index]], acc)
}

function ParseIntHelper(s: string, index: int, acc: int): int
  ensures ParseIntHelper(s, index, acc) >= 0
  decreases |s| - index
{
  if index >= |s| then acc
  else ParseIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
}

function ParseIntArrayHelper(s: string, index: int, current: string, acc: seq<int>): seq<int>
  ensures forall x :: x in ParseIntArrayHelper(s, index, current, acc) ==> x >= 0
  decreases |s| - index, |current|
{
  if index == |s| then
    if |current| > 0 then acc + [ParseIntFunc(current)] else acc
  else if s[index] == ' ' then
    ParseIntArrayHelper(s, index + 1, "", acc + [ParseIntFunc(current)])
  else
    ParseIntArrayHelper(s, index + 1, current + [s[index]], acc)
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then
    if |acc| == 0 then "0" else acc
  else
    IntToStringHelper(n / 10, ['0' + (n % 10)] + acc)
}

lemma GCDLemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a % b)
{
}

lemma SubarrayGCDProperty(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  ensures SubarrayGCD(arr, start, end) > 0
{
}

lemma GCDProperty(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma GCDPreservesPositivity(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma GCDIterative(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  ensures SubarrayGCD(arr, start, end) > 0
{
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
  var queries := new int[q];
  var i := 0;
  while i < q
    invariant 0 <= i <= q
    invariant forall j :: 0 <= j < i ==> queries[j] == ParseIntFunc(lines[3 + j])
  {
    queries[i] := ParseIntFunc(lines[3 + i]);
    i := i + 1;
  }
  
  var results := new int[q];
  i := 0;
  while i < q
    invariant 0 <= i <= q
    invariant forall j :: 0 <= j < i ==> results[j] >= 0
    invariant forall j :: 0 <= j < i ==> results[j] == CountSubarraysWithGCD(arr, queries[j])
  {
    var count := 0;
    var start := 0;
    while start < |arr|
      invariant 0 <= start <= |arr|
      invariant count >= 0
      invariant count == CountSubarraysStartingBefore(arr, queries[i], start)
    {
      var currentGCD := arr[start];
      var end := start;
      while end < |arr|
        invariant start <= end <= |arr|
        invariant currentGCD > 0
        invariant currentGCD == SubarrayGCD(arr, start, end)
        invariant count + CountSubarraysInRange(arr, queries[i], start, end) == CountSubarraysStartingBefore(arr, queries[i], start) + CountSubarraysInRange(arr, queries[i], start, end)
      {
        if currentGCD == queries[i] then {
          count := count + 1;
        }
        if end < |arr| - 1 {
          currentGCD := gcd(currentGCD, arr[end + 1]);
        }
        end := end + 1;
      }
      start := start + 1;
    }
    results[i] := count;
    i := i + 1;
  }
  
  result := FormatOutput(results[..]);
}

ghost function CountSubarraysStartingBefore(arr: seq<int>, target: int, index: int): int
  requires |arr| > 0
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  requires target > 0
  requires 0 <= index <= |arr|
  ensures CountSubarraysStartingBefore(arr, target, index) >= 0
{
  if index == 0 then 0
  else |set pair | pair in SubarrayPairs(arr) && pair.0 < index && SubarrayGCD(arr, pair.0, pair.1) == target|
}

ghost function CountSubarraysInRange(arr: seq<int>, target: int, start: int, end: int): int
  requires |arr| > 0
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  requires target > 0
  requires 0 <= start <= end <= |arr|
  ensures CountSubarraysInRange(arr, target, start, end) >= 0
{
  |set pair | pair in SubarrayPairs(arr) && pair.0 == start && pair.1 < end && SubarrayGCD(arr, pair.0, pair.1) == target|
}
// </vc-code>

