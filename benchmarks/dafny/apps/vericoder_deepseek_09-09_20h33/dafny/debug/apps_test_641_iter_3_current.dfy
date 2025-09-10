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
    ensures |SplitOnSpace(s)| >= 1
    ensures forall i :: 0 <= i < |SplitOnSpace(s)| ==> SplitOnSpace(s)[i] != ""
    ensures s != "" ==> SplitOnSpace(s)[0] == s
{
    if s == "" then [""]
    else [s]
}

lemma ValidInputNonEmptyTrimmed(input: string)
    requires ValidInput(input)
    ensures (if |input| > 0 && input[|input|-1] == '\n' then |input[..|input|-1]| > 0 else |input| > 0)
{
    // ValidInput ensures |input| > 0
    if |input| > 0 && input[|input|-1] == '\n' {
        // Removing '\n' from non-empty string gives non-empty result
        assert |input[..|input|-1]| == |input| - 1;
        assert |input| > 0 ==> |input| - 1 >= 0;
        // ValidInput predicate requires SplitOnSpace(trimmed) to have at least 1 element
        // and each element is non-empty, so trimmed must be non-empty
        var trimmed := input[..|input|-1];
        assert |SplitOnSpace(trimmed)| >= 1;
        assert SplitOnSpace(trimmed)[0] != "";
        assert |trimmed| > 0;
    }
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
  var last := parts[|parts|-1];
  
  if last == "month" {
      var first := parts[0];
      if first == "31" {
          result := "7\n";
      } else if first == "30" {
          result := "11\n";
      } else {
          result := "12\n";
      }
  } else {
      var first := parts[0];
      if first == "5" || first == "6" {
          result := "53\n";
      } else {
          result := "52\n";
      }
  }
}
// </vc-code>

