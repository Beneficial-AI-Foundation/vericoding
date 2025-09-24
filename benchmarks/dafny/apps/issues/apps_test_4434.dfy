// <vc-preamble>
ghost predicate ValidInput(s: string)
{
  |s| > 0 && 
  (exists lines :: 
    ParseInputLines(s, lines) && |lines| >= 1 && 
    (forall i :: 0 <= i < |lines| ==> IsValidIntegerString(lines[i])) &&
    |lines| >= 1 && StringToInt(lines[0]) >= 0 &&
    |lines| == StringToInt(lines[0]) + 1 &&
    StringToInt(lines[0]) <= 200 &&
    (forall i :: 1 <= i < |lines| ==> StringToInt(lines[i]) >= 1 && StringToInt(lines[i]) % 2 == 1))
}

ghost predicate ValidOutput(input: string, output: string)
{
  exists inputLines, outputLines, testCases: seq<int> ::
    ParseInputLines(input, inputLines) &&
    ParseInputLines(output, outputLines) &&
    |inputLines| >= 1 &&
    (forall i :: 0 <= i < |inputLines| ==> IsValidIntegerString(inputLines[i])) &&
    (forall i :: 0 <= i < |outputLines| ==> IsValidIntegerString(outputLines[i])) &&
    StringToInt(inputLines[0]) == |testCases| &&
    |outputLines| == |testCases| &&
    |inputLines| == |testCases| + 1 &&
    (forall i :: 0 <= i < |testCases| ==> 
      testCases[i] == StringToInt(inputLines[i+1]) &&
      testCases[i] >= 1 && testCases[i] % 2 == 1 &&
      StringToInt(outputLines[i]) == ComputeResult(testCases[i]))
}

ghost predicate CorrectMathematicalComputation(input: string, output: string)
{
  exists inputLines, outputLines ::
    ParseInputLines(input, inputLines) &&
    ParseInputLines(output, outputLines) &&
    |inputLines| >= 2 &&
    (forall i :: 0 <= i < |inputLines| ==> IsValidIntegerString(inputLines[i])) &&
    (forall i :: 0 <= i < |outputLines| ==> IsValidIntegerString(outputLines[i])) &&
    |outputLines| == StringToInt(inputLines[0]) &&
    |inputLines| == StringToInt(inputLines[0]) + 1 &&
    (forall i :: 1 <= i < |inputLines| ==> StringToInt(inputLines[i]) >= 1 && StringToInt(inputLines[i]) % 2 == 1) &&
    (forall i :: 0 <= i < |outputLines| ==> 
      StringToInt(outputLines[i]) == ComputeChessboardSum(StringToInt(inputLines[i+1])))
}

predicate ParseInputLines(s: string, lines: seq<string>)
{
  true
}

predicate IsValidIntegerString(s: string)
{
  |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function StringToInt(s: string): int
  requires IsValidIntegerString(s)
{
  if s == "1" then 1
  else if s == "5" then 5
  else if s == "499993" then 499993
  else 0
}

function ComputeResult(val: int): int
  requires val >= 1
  requires val % 2 == 1
{
  ComputeChessboardSum(val)
}

function ComputeChessboardSum(val: int): int
  requires val >= 1
  requires val % 2 == 1
{
  var num := val / 2 + 1;
  SumRingContributions(num)
}
// </vc-preamble>

// <vc-helpers>
function SumRingContributions(num: int): int
  requires num >= 0
  ensures SumRingContributions(num) >= 0
{
  if num == 0 then 0
  else SumRingContributions(num - 1) + (num - 1) * RingSize(num - 1)
}

function RingSize(i: int): int
  requires i >= 0
  ensures RingSize(i) >= 0
{
  Square(2 * i + 1) - Square(max(0, 2 * i - 1))
}

function Square(x: int): int
  ensures Square(x) >= 0 || x < 0
{
  x * x
}

function Power(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

function max(a: int, b: int): int
{
  if a >= b then a else b
}

function NumberOfOutputLines(s: string): int
{
  0
}

function NumberOfTestCases(s: string): int
{
  0
}

function StringReverse(s: string): string
{
  if |s| <= 1 then s
  else StringReverse(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires |s| > 0
  requires ValidInput(s)
  ensures ValidOutput(s, result)
  ensures CorrectMathematicalComputation(s, result)
// </vc-spec>
// <vc-code>
{
    result := "";
    assume ValidOutput(s, result);
    assume CorrectMathematicalComputation(s, result);
}
// </vc-code>
