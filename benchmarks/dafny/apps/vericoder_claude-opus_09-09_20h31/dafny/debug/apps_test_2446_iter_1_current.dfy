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
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

method GCD(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result == gcd(a, b)
  ensures result > 0
{
  var x, y := a, b;
  while x != y
    invariant x > 0 && y > 0
    invariant gcd(x, y) == gcd(a, b)
    decreases x + y
  {
    if x > y {
      x := x - y;
    } else {
      y := y - x;
    }
  }
  result := x;
}

method SubarrayGCDMethod(arr: seq<int>, start: int, end: int) returns (result: int)
  requires 0 <= start <= end < |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  ensures result == SubarrayGCD(arr, start, end)
  ensures result > 0
  decreases end - start
{
  if start == end {
    result := arr[start];
  } else {
    var rest := SubarrayGCDMethod(arr, start + 1, end);
    result := GCD(arr[start], rest);
  }
}

method CountSubarraysWithGCDMethod(arr: seq<int>, target: int) returns (count: int)
  requires |arr| > 0
  requires forall i :: 0 <= i < |arr| ==> arr[i] > 0
  requires target > 0
  ensures count == CountSubarraysWithGCD(arr, target)
  ensures count >= 0
{
  count := 0;
  for i := 0 to |arr|
    invariant 0 <= i <= |arr|
    invariant count == |set pair | pair in SubarrayPairs(arr[..i]) && SubarrayGCD(arr, pair.0, pair.1) == target|
  {
    for j := i to |arr|
      invariant i <= j <= |arr|
      invariant count == |set pair | (pair in SubarrayPairs(arr[..i]) || (pair.0 == i && pair.1 < j)) && SubarrayGCD(arr, pair.0, pair.1) == target|
    {
      var g := SubarrayGCDMethod(arr, i, j);
      if g == target {
        count := count + 1;
      }
    }
  }
}

function SplitLinesHelper(s: string, pos: int, current: string, acc: seq<string>): seq<string>
  requires 0 <= pos <= |s|
  ensures forall line :: line in SplitLinesHelper(s, pos, current, acc) ==> '\n' !in line
  decreases |s| - pos
{
  if pos == |s| then
    if |current| > 0 then acc + [current] else acc
  else if s[pos] == '\n' then
    SplitLinesHelper(s, pos + 1, "", acc + [current])
  else
    SplitLinesHelper(s, pos + 1, current + [s[pos]], acc)
}

method SplitLines(s: string) returns (lines: seq<string>)
  ensures lines == SplitLinesFunc(s)
  ensures forall line :: line in lines ==> '\n' !in line
{
  lines := [];
  var current := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant lines + (if |current| > 0 then [current] else []) == SplitLinesHelper(s, i, current, lines)
  {
    if s[i] == '\n' {
      lines := lines + [current];
      current := "";
    } else {
      current := current + [s[i]];
    }
  }
  if |current| > 0 {
    lines := lines + [current];
  }
}

function ParseIntHelper(s: string, pos: int, acc: int): int
  requires 0 <= pos <= |s|
  ensures ParseIntHelper(s, pos, acc) >= 0
  decreases |s| - pos
{
  if pos == |s| then acc
  else if '0' <= s[pos] <= '9' then
    ParseIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
  else acc
}

method ParseInt(s: string) returns (n: int)
  ensures n == ParseIntFunc(s)
  ensures n >= 0
{
  n := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant n == ParseIntHelper(s, i, n)
    invariant n >= 0
  {
    if '0' <= s[i] <= '9' {
      n := n * 10 + (s[i] as int - '0' as int);
    }
  }
}

function ParseIntArrayHelper(s: string, pos: int, current: string, acc: seq<int>): seq<int>
  requires 0 <= pos <= |s|
  ensures forall x :: x in ParseIntArrayHelper(s, pos, current, acc) ==> x >= 0
  decreases |s| - pos
{
  if pos == |s| then
    if |current| > 0 then acc + [ParseIntFunc(current)] else acc
  else if s[pos] == ' ' then
    if |current| > 0 then ParseIntArrayHelper(s, pos + 1, "", acc + [ParseIntFunc(current)])
    else ParseIntArrayHelper(s, pos + 1, "", acc)
  else
    ParseIntArrayHelper(s, pos + 1, current + [s[pos]], acc)
}

method ParseIntArray(s: string) returns (arr: seq<int>)
  ensures arr == ParseIntArrayFunc(s)
  ensures forall x :: x in arr ==> x >= 0
{
  arr := [];
  var current := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant arr + (if |current| > 0 then [ParseIntFunc(current)] else []) == ParseIntArrayHelper(s, i, current, arr)
    invariant forall x :: x in arr ==> x >= 0
  {
    if s[i] == ' ' {
      if |current| > 0 {
        var n := ParseInt(current);
        arr := arr + [n];
        current := "";
      }
    } else {
      current := current + [s[i]];
    }
  }
  if |current| > 0 {
    var n := ParseInt(current);
    arr := arr + [n];
  }
}

function IntToStringHelper(n: int, acc: string): string
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else IntToStringHelper(n / 10, ((n % 10) as char + '0' as char) as string + acc)
}

method IntToString(n: int) returns (s: string)
  requires n >= 0
  ensures s == IntToStringFunc(n)
{
  if n == 0 {
    s := "0";
  } else {
    s := "";
    var m := n;
    while m > 0
      invariant 0 <= m <= n
      invariant s == IntToStringHelper(n, s)[|IntToStringHelper(m, "")|..]
      decreases m
    {
      s := ((m % 10) as char + '0' as char) as string + s;
      m := m / 10;
    }
  }
}

method FormatOutputMethod(results: seq<int>) returns (s: string)
  requires forall x :: x in results ==> x >= 0
  ensures s == FormatOutput(results)
{
  if |results| == 0 {
    s := "";
  } else if |results| == 1 {
    s := IntToString(results[0]);
  } else {
    var first := IntToString(results[0]);
    var rest := FormatOutputMethod(results[1..]);
    s := first + "\n" + rest;
  }
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
  var lines := SplitLines(input);
  var n := ParseInt(lines[0]);
  var arr := ParseIntArray(lines[1]);
  var q := ParseInt(lines[2]);
  
  var results: seq<int> := [];
  
  for i := 0 to q
    invariant 0 <= i <= q
    invariant |results| == i
    invariant results == seq(i, j requires 0 <= j < i => CountSubarraysWithGCD(arr, ParseIntFunc(lines[3 + j])))
    invariant forall x :: x in results ==> x >= 0
  {
    var target := ParseInt(lines[3 + i]);
    var count := CountSubarraysWithGCDMethod(arr, target);
    results := results + [count];
  }
  
  result := FormatOutputMethod(results);
}
// </vc-code>

