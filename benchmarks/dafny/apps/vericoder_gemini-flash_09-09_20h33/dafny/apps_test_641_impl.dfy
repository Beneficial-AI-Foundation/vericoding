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
function SplitOnSpace(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitOnSpace(s)| ==> SplitOnSpace(s)[i] != "" && forall j :: 0 <= j < |SplitOnSpace(s)[i]| ==> SplitOnSpace(s)[i][j] != ' '
  ensures s == "" ==> |SplitOnSpace(s)| == 0
  ensures s != "" && !(' ' in s) ==> SplitOnSpace(s) == [s]
{
  if s == "" then []
  else
    var i := 0;
    while i < |s| && s[i] == ' '
      invariant 0 <= i <= |s|
      decreases |s|-i
    {
      i := i + 1;
    }
    if i == |s| then [] // string is all spaces
    else
      var j := i;
      while j < |s| && s[j] != ' '
        invariant i <= j <= |s|
        decreases |s|-j
      {
        j := j + 1;
      }
      var head := s[i..j];
      var tail := if j < |s| then SplitOnSpace(s[j..]) else [];
      [head] + tail
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
    if parts[|parts|-1] == "month" then
        if parts[0] == "31" then result := "7\n"
        else if parts[0] == "30" then result := "11\n"
        else result := "12\n"
    else
        if parts[0] == "5" || parts[0] == "6" then result := "53\n"
        else result := "52\n";
}
// </vc-code>

