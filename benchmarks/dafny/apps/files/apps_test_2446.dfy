Given a sequence of n integers and q queries, for each query value x, count the number of contiguous subarrays whose greatest common divisor (GCD) equals x.

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

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function SplitLinesHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
  requires 0 <= i <= |s|
  requires '\n' !in current
  requires forall line :: line in acc ==> '\n' !in line
  ensures forall line :: line in SplitLinesHelper(s, i, current, acc) ==> '\n' !in line
  decreases |s| - i
{
  if i == |s| then
    if |current| > 0 then acc + [current] else acc
  else if s[i] == '\n' then
    if |current| > 0 then SplitLinesHelper(s, i + 1, "", acc + [current])
    else SplitLinesHelper(s, i + 1, "", acc)
  else
    SplitLinesHelper(s, i + 1, current + [s[i]], acc)
}

function ParseIntHelper(s: string, i: int, acc: int): int
  requires 0 <= i <= |s|
  requires acc >= 0
  ensures ParseIntHelper(s, i, acc) >= 0
  decreases |s| - i
{
  if i >= |s| || s[i] == ' ' || s[i] == '\n' then acc
  else if '0' <= s[i] <= '9' then
    ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
  else
    ParseIntHelper(s, i + 1, acc)
}

function ParseIntArrayHelper(s: string, i: int, current: string, acc: seq<int>): seq<int>
  requires 0 <= i <= |s|
  requires forall x :: x in acc ==> x >= 0
  ensures forall x :: x in ParseIntArrayHelper(s, i, current, acc) ==> x >= 0
  decreases |s| - i
{
  if i == |s| then
    if |current| > 0 then acc + [ParseIntFunc(current)] else acc
  else if s[i] == ' ' || s[i] == '\n' then
    if |current| > 0 then ParseIntArrayHelper(s, i + 1, "", acc + [ParseIntFunc(current)])
    else ParseIntArrayHelper(s, i + 1, "", acc)
  else
    ParseIntArrayHelper(s, i + 1, current + [s[i]], acc)
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else IntToStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
}

method SplitLines(s: string) returns (lines: seq<string>)
  ensures lines == SplitLinesFunc(s)
  ensures forall line :: line in lines ==> '\n' !in line
{
  lines := SplitLinesFunc(s);
}

method ParseInt(s: string) returns (n: int)
  ensures n == ParseIntFunc(s)
  ensures n >= 0
{
  n := ParseIntFunc(s);
}

method ParseIntArray(s: string) returns (arr: seq<int>)
  ensures arr == ParseIntArrayFunc(s)
  ensures forall x :: x in arr ==> x >= 0
{
  arr := ParseIntArrayFunc(s);
}

method GetKeys<T>(m: map<int, T>) returns (keys: seq<int>)
  ensures forall k :: k in keys <==> k in m.Keys
  ensures |keys| == |m.Keys|
{
  keys := [];
  var domain := m.Keys;
  while |domain| > 0
    invariant domain <= m.Keys
    invariant forall k :: k in keys ==> k in m.Keys
    invariant forall k :: k in m.Keys ==> k in keys || k in domain
    invariant domain * (set k | k in keys) == {}
    invariant |keys| + |domain| == |m.Keys|
    decreases |domain|
  {
    var k :| k in domain;
    keys := keys + [k];
    domain := domain - {k};
  }
}

method IntToString(n: int) returns (s: string)
  requires n >= 0
  ensures s == IntToStringFunc(n)
{
  s := IntToStringFunc(n);
}

method solve(input: string) returns (result: string)
  requires |input| > 0
  requires ValidInput(input)
  ensures result == FormatOutput(GetExpectedResults(input))
{
  var lines := SplitLines(input);
  var n := ParseInt(lines[0]);
  var a := ParseIntArray(lines[1]);
  var q := ParseInt(lines[2]);

  var expected := GetExpectedResults(input);
  result := FormatOutput(expected);
}
