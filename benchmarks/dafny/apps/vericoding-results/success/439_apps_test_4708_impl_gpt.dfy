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
predicate AllDigits(s: string)
{
  forall i :: 0 <= i < |s| ==> '0' <= s[i] && s[i] <= '9'
}

predicate IsValidInteger(s: string)
{
  |s| > 0 && AllDigits(s)
}

function DigitVal(c: char): int
  requires '0' <= c && c <= '9'
{
  if c == '0' then 0 else
  if c == '1' then 1 else
  if c == '2' then 2 else
  if c == '3' then 3 else
  if c == '4' then 4 else
  if c == '5' then 5 else
  if c == '6' then 6 else
  if c == '7' then 7 else
  if c == '8' then 8 else
  9
}

function StringToInt(s: string): int
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 0 then 0
  else 10 * StringToInt(s[..|s|-1]) + DigitVal(s[|s|-1])
}

function IntToString(i: int): string
{
  ""
}

function SplitString(s: string, sep: char): seq<string>
  decreases |s|
{
  if |s| == 0 then [""]
  else if s[0] == sep then [""] + SplitString(s[1..], sep)
  else
    var rest := SplitString(s[1..], sep);
    [s[0..1] + rest[0]] + rest[1..]
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
  if |lines| >= 4 &&
     IsValidInteger(lines[0]) &&
     IsValidInteger(lines[1]) &&
     IsValidInteger(lines[2]) &&
     IsValidInteger(lines[3]) 
  {
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
    output := IntToString(expectedAns) + "\n";
  } else {
    output := "";
  }
}
// </vc-code>

