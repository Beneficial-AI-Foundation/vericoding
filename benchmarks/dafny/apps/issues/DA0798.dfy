// <vc-preamble>
predicate ValidInput(input: string)
{
  var lines := SplitByNewline(input);
  |lines| >= 1 &&
  var n := ParseInt(lines[0]);
  1 <= n <= 100000 &&
  |lines| >= n + 1 &&
  forall i :: 1 <= i <= n ==> ValidDayInput(lines[i])
}

predicate ValidDayInput(line: string)
{
  var parts := SplitBySpace(line);
  |parts| >= 2 &&
  var a := ParseInt(parts[0]);
  var p := ParseInt(parts[1]);
  1 <= a <= 100 && 1 <= p <= 100
}

function ComputeMinimumCost(input: string): string
  requires ValidInput(input)
  ensures |ComputeMinimumCost(input)| > 0
{
  var lines := SplitByNewline(input);
  var n := ParseInt(lines[0]);
  IntToString(ComputeCostUpToDay(lines, n, 1000000000, 0))
}

function ComputeBestPriceUpToDay(lines: seq<string>, day: int, initialBest: int): int
  requires day >= 0
  requires |lines| > day
  requires forall j :: 1 <= j <= day ==> ValidDayInput(lines[j])
  requires initialBest >= 1
  ensures ComputeBestPriceUpToDay(lines, day, initialBest) >= 1
  decreases day
{
  if day == 0 then initialBest
  else
    var parts := SplitBySpace(lines[day]);
    assert ValidDayInput(lines[day]);
    assert |parts| >= 2;
    var p := ParseInt(parts[1]);
    assert 1 <= p <= 100;
    var prevBest := ComputeBestPriceUpToDay(lines, day - 1, initialBest);
    if p < prevBest then p else prevBest
}

function ComputeCostUpToDay(lines: seq<string>, day: int, initialBest: int, initialCost: int): int
  requires day >= 0
  requires |lines| > day
  requires forall j :: 1 <= j <= day ==> ValidDayInput(lines[j])
  requires initialCost >= 0
  requires initialBest >= 1
  ensures ComputeCostUpToDay(lines, day, initialBest, initialCost) >= 0
  decreases day
{
  if day == 0 then initialCost
  else
    var parts := SplitBySpace(lines[day]);
    assert ValidDayInput(lines[day]);
    assert |parts| >= 2;
    var a := ParseInt(parts[0]);
    var p := ParseInt(parts[1]);
    assert 1 <= a <= 100;
    assert 1 <= p <= 100;
    var bestUpToPrev := ComputeBestPriceUpToDay(lines, day - 1, initialBest);
    var newBest := if p < bestUpToPrev then p else bestUpToPrev;
    var prevCost := ComputeCostUpToDay(lines, day - 1, initialBest, initialCost);
    assert prevCost >= 0;
    assert a >= 1;
    assert newBest >= 1;
    prevCost + a * newBest
}
// </vc-preamble>

// <vc-helpers>
function SplitByNewline(s: string): seq<string>
{
  if |s| == 0 then []
  else 
    var i := FindChar(s, '\n');
    if i == -1 then [s]
    else if i >= 0 && i < |s| then [s[0..i]] + SplitByNewline(s[i+1..])
    else [s]
}

function SplitBySpace(s: string): seq<string>
{
  if |s| == 0 then []
  else 
    var i := FindChar(s, ' ');
    if i == -1 then [s]
    else if i >= 0 && i < |s| then [s[0..i]] + SplitBySpace(s[i+1..])
    else [s]
}

function FindChar(s: string, c: char): int
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 
    var rest := FindChar(s[1..], c);
    if rest == -1 then -1 else 1 + rest
}

function ParseInt(s: string): int
{
  if |s| == 0 then 0
  else if |s| == 1 then 
    if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0
  else
    ParseInt(s[0..|s|-1]) * 10 + (if '0' <= s[|s|-1] <= '9' then (s[|s|-1] as int) - ('0' as int) else 0)
}

function IntToString(n: int): string
  ensures |IntToString(n)| > 0
{
  if n == 0 then "0"
  else if n < 0 then "-" + IntToStringPos(-n)
  else IntToStringPos(n)
}

function IntToStringPos(n: int): string
  requires n > 0
  ensures |IntToStringPos(n)| > 0
  decreases n
{
  if n < 10 then [('0' as int + n) as char]
  else IntToStringPos(n / 10) + [('0' as int + (n % 10)) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  requires ValidInput(input)
  ensures |result| > 0
  ensures result == ComputeMinimumCost(input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitByNewline(input);
  var n := ParseInt(lines[0]);

  var bestP := 1000000000;
  var sol := 0;

  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant bestP <= 1000000000
    invariant bestP >= 1
    invariant sol >= 0
    invariant bestP == ComputeBestPriceUpToDay(lines, i - 1, 1000000000)
    invariant sol == ComputeCostUpToDay(lines, i - 1, 1000000000, 0)
    invariant forall j :: 1 <= j <= n ==> ValidDayInput(lines[j])
    invariant |lines| >= n + 1
  {
    var parts := SplitBySpace(lines[i]);
    assert ValidDayInput(lines[i]);
    assert |parts| >= 2;
    var a := ParseInt(parts[0]);
    var p := ParseInt(parts[1]);

    if p < bestP {
      bestP := p;
    }

    sol := sol + a * bestP;
    i := i + 1;
  }

  result := IntToString(sol);
}
// </vc-code>
