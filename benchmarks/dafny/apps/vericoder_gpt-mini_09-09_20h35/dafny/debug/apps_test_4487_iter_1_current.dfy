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
function method SplitOnSpaces(s: string): seq<string>
    ensures forall w :: w in SplitOnSpaces(s) ==> |w| > 0
{
    var parts: seq<string> := [];
    var cur: string := "";
    var i := 0;
    while i < |s|
      decreases |s| - i
    {
      if s[i] == ' ' {
        if |cur| > 0 {
          parts := parts + [cur];
          cur := "";
        }
      } else {
        cur := cur + s[i..i+1];
      }
      i := i + 1;
    }
    if |cur| > 0 {
      parts := parts + [cur];
    }
    parts
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

