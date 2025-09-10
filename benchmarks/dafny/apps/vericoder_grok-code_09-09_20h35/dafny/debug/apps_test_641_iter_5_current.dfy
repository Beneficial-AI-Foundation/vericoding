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
function SkipSpaces(s: string, idx: nat): nat
  requires 0 <= idx <= |s|
  ensures 0 <= result <= |s|
  ensures result >= idx
  ensures result == |s| || s[result] != ' '
  decreases |s| - idx
{
  if idx < |s| && s[idx] == ' ' then SkipSpaces(s, idx + 1) else idx
}

function FindEnd(s: string, idx: nat): nat
  requires 0 <= idx <= |s|
  ensures 0 <= result <= |s|
  ensures result >= idx
  ensures result == |s| || s[result] == ' '
  decreases |s| - idx
{
  if idx < |s| && s[idx] != ' ' then FindEnd(s, idx + 1) else idx
}

function SplitOnSpace(s: string): seq<string>
  decreases |s|
{
  var idx := SkipSpaces(s, 0);
  if idx == |s| then [] else
    var end := FindEnd(s, idx);
    [s[idx..end]] + SplitOnSpace(s[end..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == GetExpectedResult(input)
// </vc-spec>
// <vc-code>
{
  var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
  var parts := SplitOnSpace(trimmed);
  if parts[|parts|-1] == "month" {
    if parts[0] == "31" {
      result := "7\n";
    } else if parts[0] == "30" {
      result := "11\n";
    } else {
      result := "12\n";
    }
  } else {
    if parts[0] == "5" || parts[0] == "6" {
      result := "53\n";
    } else {
      result := "52\n";
    }
  }
}
// </vc-code>

