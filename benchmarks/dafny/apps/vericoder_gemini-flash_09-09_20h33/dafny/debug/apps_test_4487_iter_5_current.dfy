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
function SplitOnSpaces(s: string): seq<string>
  ensures forall i :: 0 <= i < |ret| ==> |ret[i]| > 0
  ensures s == "" ==> ret == []
  ensures forall i :: 0 <= i < |ret| ==> ret[i] == "" ==> false
{
  if s == "" then
    []
  else
    var i := 0;
    var parts := new seq<string>();
    var currentPartStart := 0;
    while i < |s|
      decreases |s| - i
      invariant 0 <= i <= |s|
      invariant 0 <= currentPartStart <= i
      invariant (forall k :: 0 <= k < |parts| ==> |parts[k]| > 0)
      invariant (currentPartStart == 0 || (currentPartStart > 0 && s[currentPartStart-1] == ' '))
      invariant (forall k :: 0 <= k < |parts| ==> (exists start end :: 0 <= start < end <= i && parts[k] == s[start..end] && s[end-1] != ' '))
      invariant (currentPartStart <= i ==> (forall k :: currentPartStart <= k < i ==> s[k] != ' '))
    {
      if s[i] == ' '
      {
        if i > currentPartStart // Avoid adding empty strings for multiple spaces
        {
          parts := parts + [s[currentPartStart..i]];
        }
        currentPartStart := i + 1;
      }
      i := i + 1;
    }
    // Add the last part
    if i > currentPartStart
    {
      parts := parts + [s[currentPartStart..i]];
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
    if ValidParsedInput(parts) then
        if IsWordChain(parts[0], parts[1], parts[2]) then
            result := "YES\n"
        else
            result := "NO\n"
    else
        result := ""
}
// </vc-code>

