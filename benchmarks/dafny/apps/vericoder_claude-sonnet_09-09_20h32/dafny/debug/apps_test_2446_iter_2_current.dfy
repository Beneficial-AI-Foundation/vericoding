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
lemma AccumulatorPreservesProperty(acc: seq<string>)
  requires forall line :: line in acc ==> '\n' !in line
  ensures forall line :: line in acc ==> '\n' !in line
{
}

function SplitLinesHelper(s: string, index: int, current: string, acc: seq<string>): seq<string>
  requires 0 <= index <= |s|
  requires forall line :: line in acc ==> '\n' !in line
  requires '\n' !in current
  ensures forall line :: line in SplitLinesHelper(s, index, current, acc) ==> '\n' !in line
  decreases |s| - index
{
  if index == |s| then
    if |current| == 0 then (
      AccumulatorPreservesProperty(acc);
      acc
    ) else (
      AccumulatorPreservesProperty(acc);
      acc + [current]
    )
  else if s[index] == '\n' then
    SplitLinesHelper(s, index + 1, "", acc + [current])
  else
    SplitLinesHelper(s, index + 1, current + [s[index]], acc)
}

function ParseIntHelper(s: string, index: int, acc: int): int
  requires 0 <= index <= |s|
  requires acc >= 0
  ensures ParseIntHelper(s, index, acc) >= 0
  decreases |s| - index
{
  if index == |s| then acc
  else if '0' <= s[index] <= '9' then
    ParseIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
  else
    acc
}

lemma AccumulatorPreservesIntProperty(acc: seq<int>)
  requires forall x :: x in acc ==> x >= 0
  ensures forall x :: x in acc ==> x >= 0
{
}

function ParseIntArrayHelper(s: string, index: int, current: string, acc: seq<int>): seq<int>
  requires 0 <= index <= |s|
  requires forall x :: x in acc ==> x >= 0
  ensures forall x :: x in ParseIntArrayHelper(s, index, current, acc) ==> x >= 0
  decreases |s| - index
{
  if index == |s| then
    if |current| == 0 then (
      AccumulatorPreservesIntProperty(acc);
      acc
    ) else (
      AccumulatorPreservesIntProperty(acc);
      acc + [ParseIntFunc(current)]
    )
  else if s[index] == ' ' then
    if |current| == 0 then
      ParseIntArrayHelper(s, index + 1, "", acc)
    else
      ParseIntArrayHelper(s, index + 1, "", acc + [ParseIntFunc(current)])
  else
    ParseIntArrayHelper(s, index + 1, current + [s[index]], acc)
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else IntToStringHelper(n / 10, [(n % 10 + '0' as int) as char] + acc)
}

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a && gcd(a, b) <= b
  decreases if a > b then a else b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
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
  var i := 0;
  
  while i < q
    invariant 0 <= i <= q
    invariant |results| == i
    invariant forall x :: x in results ==> x >= 0
    invariant forall j :: 0 <= j < i ==> results[j] == CountSubarraysWithGCD(arr, ParseIntFunc(lines[3 + j]))
  {
    var target := ParseIntFunc(lines[3 + i]);
    var count := CountSubarraysWithGCD(arr, target);
    results := results + [count];
    i := i + 1;
  }
  
  assert i == q;
  assert |results| == q;
  assert forall j :: 0 <= j < q ==> results[j] == CountSubarraysWithGCD(arr, ParseIntFunc(lines[3 + j]));
  assert results == GetExpectedResults(input);
  
  result := FormatOutput(results);
}
// </vc-code>

