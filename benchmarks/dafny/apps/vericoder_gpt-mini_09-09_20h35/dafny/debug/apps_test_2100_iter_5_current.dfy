predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 1 &&
    IsValidNumber(lines[0]) &&
    var n := StringToInt(lines[0]);
    n >= 0 && n + 1 <= |lines| &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
}

predicate ValidOutput(output: string)
{
    IsValidNumber(output)
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidDoorState(s: string)
{
    s == "0" || s == "1"
}

function CalculateMinOperations(input: string): string
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    if n == 0 then "0"
    else
        var leftZeros := CountLeftZeros(lines, 1, n);
        var rightZeros := CountRightZeros(lines, 1, n);
        var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
        var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
        IntToString(leftOps + rightOps)
}

// <vc-helpers>
function SplitAux(s: string, delim: char, i: int, tokStart: int): seq<string>
  decreases |s| - i
{
  if i >= |s| then
    if tokStart >= |s| then [] else [s[tokStart..|s|]]
  else if s[i] == delim then
    var token := if tokStart == i then "" else s[tokStart..i];
    seq{token} + SplitAux(s, delim, i + 1, i + 1)
  else
    SplitAux(s, delim, i + 1, tokStart)
}

function Split(s: string, delim: char): seq<string>
{
  if |s| == 0 then [""]
  else SplitAux(s, delim, 0, 0)
}

function IndexOfDelim(s: string, delim: char, i: int): int
  decreases |s| - i
{
  if i >= |s| then -1
  else if s[i] == delim then i
  else IndexOfDelim(s, delim, i + 1)
}

function StringToInt(s: string): int
  requires IsValidNumber(s)
  ensures result >= 0
  ensures IntToString(result) == s
{
  if |s| == 0 then 0
  else StringToInt(s[..|s|-1]) * 10 + (ord(s[|s|-1]) - ord('0'))
}

function IntToStringAux(i: int): string
  requires i > 0
  decreases i
{
  if i < 10 then "" + char(ord('0') + i)
  else IntToStringAux(i / 10) + ("" + char(ord('0') + i % 10))
}

function IntToString(i: int): string
  requires i >= 0
  ensures IsValidNumber(result)
  ensures StringToInt(result) == i
{
  if i == 0 then "0" else IntToStringAux(i)
}

function CountLeftZeros(lines: seq<string>, start: int, n: int): int
  requires 0 <= start <= |lines|
  requires 0 <= n
  requires start + n <= |lines|
  ensures 0 <= result <= n
  decreases n
{
  if n == 0 then 0
  else
    var head := lines[start];
    var add := if |head| > 0 && head[0] == '0' then 1 else 0;
    add + CountLeftZeros(lines, start + 1, n - 1)
}

function CountRightZeros(lines: seq<string>, start: int, n: int): int
  requires 0 <= start <= |lines|
  requires 0 <= n
  requires start + n <= |lines|
  ensures 0 <= result <= n
  decreases n
{
  if n == 0 then 0
  else
    var head := lines[start];
    var idx := IndexOfDelim(head, ' ', 0);
    // ValidInput guarantees there is a space and a second token, so idx >= 0 and idx + 1 < |head|
    var add := if idx >= 0 && idx + 1 < |head| && head[idx + 1] == '0' then 1 else 0;
    add + CountRightZeros(lines, start + 1, n - 1)
}
// </vc-helpers>

// <vc-spec>
method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures result == CalculateMinOperations(input)
// </vc-spec>
// <vc-code>
{
  result := CalculateMinOperations(input);
}
// </vc-code>

