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
  decreases |s|
{
  if |s| == 0 then
    [""]
  else if exists i :: 0 <= i < |s| && s[i] == sep then
    var firstSplit := 0;
    while firstSplit < |s| && s[firstSplit] != sep
      decreases |s| - firstSplit
      invariant 0 <= firstSplit <= |s|
    {
      firstSplit := firstSplit + 1;
    }
    [s[0..firstSplit]] + split(s[firstSplit+1..], sep)
  else
    [s]
}

function parseInteger(s: string): int
  requires s != "" && exists i :: 0 <= i < |s| && '0' <= s[i] <= '9'
  ensures intToString(parseInteger(s)) == s
  decreases |s|
{
  if |s| == 1 then
    s[0] - '0'
  else
    var digit := s[0] - '0';
    var rest := parseInteger(s[1..]);
    digit * (pow(10, |s| - 1)) + rest
}

function intToString(n: int): string
  ensures parseInteger(intToString(n)) == n
  decreases n
{
  if n == 0 then
    "0"
  else
    var lastDigit := (n % 10) as char;
    var remaining := n / 10;
    if remaining == 0 then
      [lastDigit + '0']
    else
      intToString(remaining) + [lastDigit + '0']
}

function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then 1 else base * pow(base, exponent - 1)
}

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

lemma SplitCharacterAbsent(s: string, sep: char)
  requires forall i :: 0 <= i < |s| ==> s[i] != sep
  ensures |split(s, sep)| == 1 && split(s, sep)[0] == s
{
}

lemma CharacterInString(s: string, c: char)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == c || forall i :: 0 <= i < |s| ==> s[i] != c
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  if (ValidCommandInput(input)) {
    var lines := split(input, '\n');
    var n := parseInteger(lines[0]);
    result := intToString(n + 1) + "\n";
  } else {
    result := "";
  }
}
// </vc-code>

