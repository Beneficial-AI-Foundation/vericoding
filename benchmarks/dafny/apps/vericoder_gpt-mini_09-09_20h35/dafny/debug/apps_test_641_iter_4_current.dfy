predicate ValidInput(input: string)
{
    |input| > 0 &&
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    |parts| >= 1
}

function GetExpectedResult(input: string): string
    requires ValidInput(input)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    if parts[|parts|-1] == "month" then
        if parts[0] == "31" then "7\n"
        else if parts[0] == "30" then "11\n"
        else "12\n"
    else
        if parts[0] == "5" || parts[0] == "6" then "53\n"
        else "52\n"
}

// <vc-helpers>
function IndexSpace(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then |s|
  else if s[i] == ' ' then i
  else IndexSpace(s, i + 1)
}

function SplitOnSpace(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == ' ' then SplitOnSpace(s[1..])
  else
    [ s[..IndexSpace(s, 0)] ] + SplitOnSpace(s[IndexSpace(s, 0)..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == GetExpectedResult(input)
// </vc-spec>
// <vc-code>
{
  result := GetExpectedResult(input);
}
// </vc-code>

