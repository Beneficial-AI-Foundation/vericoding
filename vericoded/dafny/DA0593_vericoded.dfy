predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidParsedInput(parts: seq<string>)
{
    |parts| == 3 && |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
}

predicate IsWordChain(a: string, b: string, c: string)
    requires |a| > 0 && |b| > 0 && |c| > 0
{
    a[|a|-1] == b[0] && b[|b|-1] == c[0]
}

function ExpectedResult(input: string): string
    requires ValidInput(input)
{
    var stripped := if |input| > 0 && input[|input|-1] == '\n' then input[0..|input|-1] else input;
    var parts := SplitOnSpaces(stripped);
    if ValidParsedInput(parts) then
        if IsWordChain(parts[0], parts[1], parts[2]) then "YES\n" else "NO\n"
    else
        ""
}

// <vc-helpers>
function IndexOfSpace(s: string): nat
  ensures 0 <= IndexOfSpace(s) <= |s|
  ensures forall k :: 0 <= k < IndexOfSpace(s) ==> s[k] != ' '
  ensures IndexOfSpace(s) < |s| ==> s[IndexOfSpace(s)] == ' '
  ensures |s| > 0 && s[0] != ' ' ==> IndexOfSpace(s) > 0
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == ' ' then 0
  else 1 + IndexOfSpace(s[1..])
}

function SplitOnSpaces(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitOnSpaces(s)| ==> |SplitOnSpaces(s)[i]| > 0
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == ' ' then SplitOnSpaces(s[1..])
  else
    var j := IndexOfSpace(s);
    var token := s[0..j];
    var restStart := if j == |s| then j else j + 1;
    [token] + SplitOnSpaces(s[restStart..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedResult(input)
    ensures result == "YES\n" || result == "NO\n" || result == ""
// </vc-spec>
// <vc-code>
{
  var stripped := if |input| > 0 && input[|input|-1] == '\n' then input[0..|input|-1] else input;
  var parts := SplitOnSpaces(stripped);
  if ValidParsedInput(parts) {
    if IsWordChain(parts[0], parts[1], parts[2]) {
      result := "YES\n";
    } else {
      result := "NO\n";
    }
  } else {
    result := "";
  }
}
// </vc-code>

