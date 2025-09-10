predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
function split(s: string, sep: char): seq<string>
  ensures |split(s, sep)| >= 1
  ensures forall i :: 0 <= i < |split(s, sep)| ==> split(s, sep)[i] != ""

function parseInteger(s: string): int
  requires s != "" && exists i :: 0 <= i < |s| && '0' <= s[i] <= '9'
  ensures intToString(parseInteger(s)) == s

function intToString(n: int): string
  ensures parseInteger(intToString(n)) == n

predicate isValidInteger(s: string) {
  s != "" && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

lemma SplitContainsNewline(s: string, sep: char)
  requires exists i :: 0 <= i < |s| && s[i] == sep
  ensures |split(s, sep)| >= 2
{
}

lemma ParseIntegerValid(s: string)
  requires isValidInteger(s)
  ensures parseInteger(s) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  var lines := split(input, '\n');
  if |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0]) {
    var n := parseInteger(lines[0]);
    result := intToString(n + 1) + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

