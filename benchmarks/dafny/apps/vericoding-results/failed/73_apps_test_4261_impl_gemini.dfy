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
function find_non_space(s: string, from: int): int
  requires 0 <= from <= |s|
  ensures from <= find_non_space(s, from) <= |s|
  ensures find_non_space(s, from) < |s| ==> s[find_non_space(s, from)] != ' '
  ensures forall i :: from <= i < find_non_space(s, from) ==> s[i] == ' '
  decreases |s| - from
{
  if from < |s| && s[from] == ' ' then
    find_non_space(s, from + 1)
  else
    from
}

function find_space(s: string, from: int): int
  requires 0 <= from <= |s|
  ensures from <= find_space(s, from) <= |s|
  ensures find_space(s, from) < |s| ==> s[find_space(s, from)] == ' '
  ensures forall i :: from <= i < find_space(s, from) ==> s[i] != ' '
  decreases |s| - from
{
  if from < |s| && s[from] != ' ' then
    find_space(s, from + 1)
  else
    from
}

function SplitOnSpaces(s: string):
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
function find_non_space(s: string, from: int): int
  requires 0 <= from <= |s|
  ensures from <= find_non_space(s, from) <= |s|
  ensures find_non_space(s, from) < |s| ==> s[find_non_space(s, from)] != ' '
  ensures forall i :: from <= i < find_non_space(s, from) ==> s[i] == ' '
  decreases |s| - from
{
  if from < |s| && s[from] == ' ' then
    find_non_space(s, from + 1)
  else
    from
}

function find_space(s: string, from: int): int
  requires 0 <= from <= |s|
  ensures from <= find_space(s, from) <= |s|
  ensures find_space(s, from) < |s| ==> s[find_space(s, from)] == ' '
  ensures forall i :: from <= i < find_space(s, from) ==> s[i] != ' '
  decreases |s| - from
{
  if from < |s| && s[from] != ' ' then
    find_space(s, from + 1)
  else
    from
}

function SplitOnSpaces(s: string):
// </vc-code>

