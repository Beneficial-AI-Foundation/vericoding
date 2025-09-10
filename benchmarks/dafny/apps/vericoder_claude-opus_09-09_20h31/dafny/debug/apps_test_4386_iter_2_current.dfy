predicate ValidInput(input: string)
{
  |input| > 0 &&
  (exists i :: 0 < i < |input| && input[i] == '\n') &&
  (forall i :: 0 <= i < |input| ==> input[i] == '\n' || ('0' <= input[i] <= '9') || ('a' <= input[i] <= 'z')) &&
  (exists i :: 0 < i < |input| && input[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9'))
}

predicate ValidParsedInput(a: int, s: string)
{
  2800 <= a < 5000 &&
  1 <= |s| <= 10 &&
  (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z')
}

predicate CorrectOutput(a: int, s: string, result: string)
{
  (a >= 3200 ==> result == s + "\n") &&
  (a < 3200 ==> result == "red\n")
}

// <vc-helpers>
function findNewline(input: string, i: int): int
  requires ValidInput(input)
  requires 0 <= i <= |input|
  ensures 0 < findNewline(input, i) < |input|
  ensures input[findNewline(input, i)] == '\n'
  ensures forall j :: i <= j < findNewline(input, i) ==> input[j] != '\n'
  decreases |input| - i
{
  if i >= |input| then
    |input| - 1  // This shouldn't happen with ValidInput
  else if input[i] == '\n' then
    i
  else
    findNewline(input, i + 1)
}

function parseInput(input: string): (int, string)
  requires ValidInput(input)
  ensures var (a, s) := parseInput(input);
    ValidParsedInput(a, s)
{
  var i := findNewline(input, 0);
  var a := stringToInt(input[..i]);
  var s := if i + 1 < |input| then input[i+1..] else "";
  (a, s)
}

function stringToInt(s: string): int
  requires |s| > 0
  requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    stringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires ValidInput(input)
  requires exists a: int, s: string :: 
    parseInput(input) == (a, s) && ValidParsedInput(a, s)
  ensures exists a: int, s: string :: 
    parseInput(input) == (a, s) && 
    ValidParsedInput(a, s) &&
    CorrectOutput(a, s, result)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a >= 3200) ==> 
    (exists s: string :: result == s + "\n" && 1 <= |s| <= 10 && (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z'))
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a < 3200) ==> result == "red\n"
// </vc-spec>
// <vc-code>
{
  var (a, s) := parseInput(input);
  
  if a >= 3200 {
    result := s + "\n";
  } else {
    result := "red\n";
  }
}
// </vc-code>

