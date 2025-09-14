predicate ValidInput(a: int, b: int, c: int)
{
    1 <= b <= a <= 20 && 1 <= c <= 20
}

function RemainingWater(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    if remaining >= 0 then remaining else 0
}

// <vc-helpers>
function NextSpace(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then i
  else if s[i] == ' ' then i
  else NextSpace(s, i + 1)
}

function SplitOnSpacesFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then []
  else
    var j := NextSpace(s, i);
    if j == i then SplitOnSpacesFrom(s, i + 1)
    else if j == |s| then [ s[i .. j] ]
    else [ s[i .. j] ] + SplitOnSpacesFrom(s, j + 1)
}

function SplitOnSpaces(s: string): seq<string>
{
  SplitOnSpacesFrom(s, 0)
}

function StringToInt(s: string): int
{
  if s == "0" then 0
  else if s == "1" then 1
  else if s == "2" then 2
  else if s == "3" then 3
  else if s == "4" then 4
  else if s == "5" then 5
  else if s == "6" then 6
  else if s == "7" then 7
  else if s == "8" then 8
  else if s == "9" then 9
  else if s == "10" then 10
  else if s == "11" then 11
  else if s == "12" then 12
  else if s == "13" then 13
  else if s == "14" then 14
  else if s == "15" then 15
  else if s == "16" then 16
  else if s == "17" then 17
  else if s == "18" then 18
  else if s == "19" then 19
  else if s == "20" then 20
  else 0
}

function IntToString(n: int): string
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else if n == 2 then "2"
  else if n == 3 then "3"
  else if n == 4 then "4"
  else if n == 5 then "5"
  else if n == 6 then "6"
  else if n == 7 then "7"
  else if n == 8 then "8"
  else if n == 9 then "9"
  else if n == 10 then "10"
  else if n == 11 then "11"
  else if n == 12 then "12"
  else if n == 13 then "13"
  else if n == 14 then "14"
  else if n == 15 then "15"
  else if n == 16 then "16"
  else if n == 17 then "17"
  else if n == 18 then "18"
  else if n == 19 then "19"
  else if n == 20 then "20"
  else ""
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
            var parts := SplitOnSpaces(trimmed);
            var a := StringToInt(parts[0]);
            var b := StringToInt(parts[1]);
            var c := StringToInt(parts[2]);
            result == IntToString(RemainingWater(a, b, c)) + "\n"
// </vc-spec>
// <vc-code>
{
  var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
  var parts := SplitOnSpaces(trimmed);
  var a := StringToInt(parts[0]);
  var b := StringToInt(parts[1]);
  var c := StringToInt(parts[2]);
  var ans := RemainingWater(a, b, c);
  return IntToString(ans) + "\n";
}
// </vc-code>

