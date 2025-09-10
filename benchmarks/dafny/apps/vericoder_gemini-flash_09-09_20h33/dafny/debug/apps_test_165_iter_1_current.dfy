function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}

// <vc-helpers>
function TrimNewline(s: string): string
  ensures s == "" || (s[|s|-1] == '\n' <==> |TrimNewline(s)| == |s|-1)
  ensures s != "" && s[|s|-1] != '\n' ==> TrimNewline(s) == s
{
  if s != "" && s[|s|-1] == '\n' then s[..|s|-1] else s
}

function SplitSpaces(s: string): seq<string>
  ensures forall x :: x in SplitSpaces(s) ==> !x.Contains(' ')
{
  if s == "" then []
  else
    var i := 0;
    while i < |s| && s[i] == ' '
      invariant 0 <= i <= |s|
    {
      i := i + 1;
    }
    var j := i;
    while j < |s| && s[j] != ' '
      invariant i <= j <= |s|
    {
      j := j + 1;
    }
    if j == |s| && i == 0 then [s]
    else if i == |s| then []
    else if i == j then [s[i..]] + SplitSpaces(s[j..])
    else [s[i..j]] + SplitSpaces(s[j..])
}

function StringToInt(s: string): int
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  requires |s| > 0
  ensures StringToInt(s) >= 0
{
  var x := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant x == (if i == 0 then 0 else (StringToInt(s[..i])))
  {
    x := x * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  x
}

function IntToString(input: int): string
  requires input >= 0
  ensures (input == 0) ==> (IntToString(input) == "0")
  ensures (input > 0) ==> (StringToInt(IntToString(input)) == input)
{
  if input == 0 then "0"
  else
    var s := "";
    var num := input;
    while num > 0
      invariant num >= 0
      invariant (s == "" && num == input) || (StringToInt(IntToString(num) + s) == input)
    {
      s := (num % 10 as char + '0' as char) + s;
      num := num / 10;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
  var parts := SplitSpaces(TrimNewline(input));
  var resultValue: int;

  if |parts| >= 3 then
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    var maxVal := Max3(a, b, c);
    var threshold := maxVal - 1;

    var missedA := if a < threshold then threshold - a else 0;
    var missedB := if b < threshold then threshold - b else 0;
    var missedC := if c < threshold then threshold - c else 0;

    resultValue := missedA + missedB + missedC;
  else
    resultValue := 0;

  result := IntToString(resultValue);
}
// </vc-code>

