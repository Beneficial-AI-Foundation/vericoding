predicate ValidInput(input: string)
{
    var lines := SplitString(input, '\n');
    |lines| >= 4 &&
    IsValidInteger(lines[0]) &&
    IsValidInteger(lines[1]) &&
    IsValidInteger(lines[2]) &&
    IsValidInteger(lines[3]) &&
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitString(input, '\n');
    if |lines| >= 4 && 
       IsValidInteger(lines[0]) &&
       IsValidInteger(lines[1]) &&
       IsValidInteger(lines[2]) &&
       IsValidInteger(lines[3]) then
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
    else
        output == ""
}

// <vc-helpers>
function FindPosition(s: string, c: char, start: int): int
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start == |s| then |s|
  else if s[start] == c then start
  else FindPosition(s, c, start + 1)
}

function SplitString(s: string, sep: char): seq<string>
{
  if |s| == 0 then []
  else
    var p := FindPosition(s, sep, 0);
    if p == |s| then [s]
    else
      [s[0..p]] + SplitString(s[p + 1..], sep)
}

function IsValidInteger(s: string): bool
{
  if |s| == 0 then false
  else if |s| == 1 && '0' <= s[0] <= '9' then true
  else if s[0] == '-' then |s| > 1 && '0' <= s[1] <= '9' && forall i :: 1 < i < |s| ==> '0' <= s[i] <= '9'
  else if '0' <= s[0] <= '9' then forall i :: 0 < i < |s| ==> '0' <= s[i] <= '9'
  else false
}

function StringToIntNumerical(s: string, acc: int): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then acc
  else StringToIntNumerical(s[1..], acc * 10 + (s[0] as int - ('0' as int)))
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if |s| == 0 then 0
  else if s[0] == '-' then -StringToIntNumerical(s[1..], 0)
  else StringToIntNumerical(s, 0)
}

function IntToString(i: int): string
{
  if i == 0 then "0"
  else if i < 0 then "-" + IntToStringPositive(-i, [])
  else IntToStringPositive(i, [])
}

function IntToStringPositive(i: int, acc: string): string
  requires i >= 0
  decreases i
{
  if i == 0 then acc
  else IntToStringPositive(i / 10, [ (('0' as int + i % 10) as char) ] + acc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidOutput(output, input)
    ensures ValidInput(input) ==> 
        var lines := SplitString(input, '\n');
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 ==>
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
// </vc-spec>
// <vc-code>
{
  var lines := SplitString(input, '\n');
  if |lines| < 4 {
    return "";
  }
  if !IsValidInteger(lines[0]) || !IsValidInteger(lines[1]) || !IsValidInteger(lines[2]) || !IsValidInteger(lines[3]) {
    return "";
  }
  var N := StringToInt(lines[0]);
  var K := StringToInt(lines[1]);
  var X := StringToInt(lines[2]);
  var Y := StringToInt(lines[3]);
  var expected := if K < N then K * X + (N - K) * Y else N * X;
  return IntToString(expected) + "\n";
}
// </vc-code>

