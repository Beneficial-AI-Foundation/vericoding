predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    var inputPairs := GetInputPairs(input);
    var expectedResults := seq(|inputPairs|, i requires 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0);
    output == FormatResults(expectedResults)
}

function ComputeMinimumCost(c: int, s: int): int
    requires c > 0 && s >= 0
    ensures ComputeMinimumCost(c, s) >= 0
{
    var a := s / c;
    var r := s % c;
    (c - r) * a * a + r * (a + 1) * (a + 1)
}

function GetInputPairs(input: string): seq<(int, int)>
    requires |input| > 0
    ensures |GetInputPairs(input)| >= 0
{
    var lines := SplitLines(input);
    if |lines| == 0 then []
    else 
        var n := ParseInt(lines[0]);
        GetPairsFromLines(lines, 1, n)
}

function FormatResults(results: seq<int>): string
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResults(results)| >= 0
{
    FormatResultsHelper(results, 0, "")
}

// <vc-helpers>
function FindIndexOf(s: seq<char>, c: char, start: nat): int
  decreases |s| - start
  ensures if FindIndexOf(s, c, start) == -1 then forall i :: start <= i < |s| ==> s[i] != c
          else 0 <= FindIndexOf(s, c, start) < |s| && FindIndexOf(s, c, start) >= start && s[FindIndexOf(s, c, start)] == c
{
  if start >= |s| then -1
  else if s[start] == c then start
  else FindIndexOf(s, c, start + 1)
}

function SplitLines(input: string): seq<string>
{
  SplitLinesAccumulator(input, [])
}

function SplitLinesAccumulator(remaining: string, acc: seq<string>): seq<string>
  decreases |remaining|
{
  if |remaining| == 0 then acc
  else
    var crIndex := FindIndexOf(remaining, '\n', 0);
    if crIndex == -1 then acc + [remaining]
    else
      var currentLine := remaining[..crIndex];
      var nextRemaining := remaining[crIndex + 1..];
      SplitLinesAccumulator(nextRemaining, acc + [currentLine])
}

function IsAllDigits(s: string): bool
  decreases |s|
{
  if |s| == 0 then true
  else if s[0] < '0' || s[0] > '9' then false
  else IsAllDigits(s[1..])
}

function ParseInt(s: string): int
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  decreases |s|
{
  if #|s| == 0 then 0
  else if |s| == 1 then (s[0] as int) - ('0' as int)
  else 10 * ParseInt(s[..|s| - 1]) + ((s[|s| - 1] as int) - ('0' as int))
}

function GetPairsFromLines(lines: seq<string>, startIndex: int, n: int): seq<(int, int)>
  requires 0 <= startIndex && 0 <= n && startIndex + 2 * n <= |lines|
  requires forall j :: 0 <= j < n ==> IsAllDigits(lines[startIndex + 2*j]) && IsAllDigits(lines[startIndex + 2*j + 1])
  decreases n
{
  GetPairsFromLinesAccumulator(lines, startIndex, n, [])
}

function GetPairsFromLinesAccumulator(lines: seq<string>, startIndex: int, n: int, acc: seq<(int, int)>): seq<(int, int)>
  requires 0 <= startIndex && 0 <= n
  decreases n
{
  if n == 0 then acc
  else
    var c := ParseInt(lines[startIndex]);
    var s := ParseInt(lines[startIndex + 1]);
    GetPairsFromLinesAccumulator(lines, startIndex + 2, n - 1, acc + [(c, s)])
}

function IntAsString(i: nat): seq<char>
{
  if i == 0 then ['0']
  else IntToStringHelper(i, [])
}

function IntToStringHelper(n: nat, acc: seq<char>): seq<char>
  decreases n
{
  if n == 0 then acc
  else
    var d := (n % 10) as int;
    var charD := (('0' as int) + d) as char;
    IntToStringHelper(n / 10, [charD] + acc)
}

function FormatResultsHelper(results: seq<int>, index: int, acc: string): string
  requires 0 <= index <= |results|
  requires forall j :: 0 <= j < |results| ==> results[j] >= 0
  decreases |results| - index
{
  if index == |results| then acc
  else
    var currentStr := IntAsString(results[index] as nat);
    var newAcc := if index == 0 then currentStr else acc + "\n" + currentStr;
    FormatResultsHelper(results, index + 1, newAcc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  var inputPairs := GetInputPairs(input);
  var results: seq<int> := [];
  var i := 0;
  while i < |inputPairs|
  {
    var c := inputPairs[i].0;
    var s := inputPairs[i].1;
    var cost := if c > 0 && s >= 0 then ComputeMinimumCost(c, s) else 0;
    results := results + [cost];
    i := i + 1;
  }
  result := FormatResults(results);
}
// </vc-code>

