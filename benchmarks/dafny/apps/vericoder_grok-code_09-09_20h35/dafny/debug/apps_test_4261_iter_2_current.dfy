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
function SplitFirst(s: string): (string, string)
{
  if |s| == 0 then ("", "")
  else if s[0] == ' ' then ("", s[1..])
  else var (w, rest) := SplitFirst(s[1..]);
       ([s[0]] + w, rest)
}

function SplitOnSpaces(s: string): seq<string>
{
  if |s| == 0 then []
  else if s[0] == ' ' then SplitOnSpaces(s[1..])
  else var (w, rest) := SplitFirst(s);
       [w] + SplitOnSpaces(rest)
}

function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else 10 * StringToInt(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(n: int): string
  requires 0 <= n <= 20
{
  if n == 0 then "0"
  else if n < 10 then [((n + ('0' as int)) as char)]
  else IntToString(n / 10) + [(((n % 10) + ('0' as int)) as char)]
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
  var remaining := RemainingWater(a, b, c);
  var result_str := IntToString(remaining) + "\n";
  result := result_str;
}
// </vc-code>

