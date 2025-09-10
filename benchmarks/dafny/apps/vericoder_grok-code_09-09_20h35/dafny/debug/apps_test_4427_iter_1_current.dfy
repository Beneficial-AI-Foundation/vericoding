predicate ValidInput(input: string)
    requires |input| > 0
{
    var tokens := parseInputPure(input);
    |tokens| == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] <= 200
}

function calculateRecurrence(r: int, D: int, x0: int, n: int): int
    requires n >= 1
    decreases n
{
    if n == 1 then r * x0 - D
    else r * calculateRecurrence(r, D, x0, n - 1) - D
}

function generateExpectedOutput(r: int, D: int, x0: int): string
{
    generateOutputUpToIteration(r, D, x0, 10)
}

function generateOutputUpToIteration(r: int, D: int, x0: int, iterations: int): string
    requires iterations >= 0
{
    if iterations == 0 then ""
    else 
        var currentValue := calculateRecurrence(r, D, x0, iterations);
        var previousOutput := generateOutputUpToIteration(r, D, x0, iterations - 1);
        previousOutput + intToString(currentValue) + "\n"
}

// <vc-helpers>
function {:opaque} intToString(i: int): string
  decreases if i < 0 then -i else i
{
  if i == 0 then "0"
  else if i < 0 then "-" + intToString(-i)
  else intToString(i / 10) + char(i % 10 + 48)
}

function charToDigit(c: char): int
  requires '0' <= c <= '9'
{
  c as int - '0' as int
}

function stringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == '-' then -stringToInt(s[1..])
  else stringToInt(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function split(s: string, delim: char): seq<string>
  decreases |s|
{
  var res := [];
  var current := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| >= 0
    decreases |s| - i
  {
    if s[i] != delim {
      current := current + [s[i]];
    } else {
      if current != "" {
        res := res + [current];
        current := "";
      }
    }
    i := i + 1;
  }
  if current != "" {
    res := res + [current];
  }
  res
}

function parseInputPure(input: string): seq<int>
{
  var tokens := split(input, ' ');
  var r := stringToInt(tokens[0]);
  var D := stringToInt(tokens[1]);
  var x0 := stringToInt(tokens[2]);
  [r, D, x0]
}

lemma ParseLemma(input: string)
  requires ValidInput(input)
  ensures |parseInputPure(input)| == 3
{
  // Proof follows from ValidInput and parse implementation
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures var tokens := parseInputPure(input);
            result == generateExpectedOutput(tokens[0], tokens[1], tokens[2])
// </vc-spec>
// <vc-code>
{
  var tokens := parseInputPure(input);
  var r := tokens[0];
  var D := tokens[1];
  var x0 := tokens[2];
  result := generateExpectedOutput(r, D, x0);
}
// </vc-code>

