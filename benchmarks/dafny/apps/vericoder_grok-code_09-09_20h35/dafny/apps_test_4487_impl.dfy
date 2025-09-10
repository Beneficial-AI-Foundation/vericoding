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
function IndexOfSpace(s: string, idx: nat): nat
  requires 0 <= idx <= |s|
  decreases |s| - idx
  ensures 0 <= idx <= IndexOfSpace(s, idx) <= |s| && forall i :: idx <= i < IndexOfSpace(s, idx) ==> s[i] != ' ' 
  ensures IndexOfSpace(s, idx) == |s| || s[IndexOfSpace(s, idx)] == ' '
{
  if idx == |s| then |s|
  else if s[idx] == ' ' then idx
  else IndexOfSpace(s, idx + 1)
}

function SplitOnSpaces(s: string): seq<string>
{
  SplitAux(s)
}

function SplitAux(s: string): seq<string>
{
  if |s| == 0 then []
  else if s[0] == ' ' then SplitAux(s[1..])
  else
    var end := IndexOfSpace(s, 0);
    if end == |s| then [s]
    else [s[0..end]] + SplitAux(s[end + 1..])
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
  var stripped := if |input| > 0 && input[|input| - 1] == '\n' then input[..|input| - 1] else input;
  var parts := SplitOnSpaces(stripped);
  result := if ValidParsedInput(parts) then
    if IsWordChain(parts[0], parts[1], parts[2]) then "YES\n" else "NO\n"
  else
    "";
}
// </vc-code>

