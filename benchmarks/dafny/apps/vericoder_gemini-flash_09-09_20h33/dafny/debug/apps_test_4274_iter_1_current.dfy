predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists lines :: lines == Split(input, '\n') && |lines| > 0 &&
    exists parts :: parts == Split(lines[0], ' ') && |parts| == 2 &&
    exists n, m :: n == StringToInt(parts[0]) && 
                   m == StringToInt(parts[1]) &&
                   1 <= n <= 100 && 0 <= m <= n
}

function ExtractN(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[0])
}

function ExtractM(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[1])
}

predicate CorrectOutput(input: string, result: string)
requires ValidInput(input)
{
    var n := ExtractN(input);
    var m := ExtractM(input);
    (n == m ==> result == "Yes") && (n != m ==> result == "No")
}

// <vc-helpers>
function StringToInt(s: string): int
requires s != ""
reads s
{
  if s[0] == '-' then
    -StringToInt(s[1..])
  else if '0' <= s[0] <= '9' then
    (s[0] as int - '0' as int) + (if |s| > 1 then 10 * StringToInt(s[1..]) else 0)
  else
    0 // Should not happen with valid input, but needed for termination
}

function Split(s: string, separator: char): seq<string>
  ensures forall i :: 0 <= i < |Split(s, separator)| ==> |Split(s, separator)[i]| >= 0
{
  if s == "" then
    if separator == '\n' then
      <""> // Special case for empty string and newline separator, common in Advent of Code inputs
    else
      <"">
  else
    var i := 0;
    while i < |s| && s[i] != separator
      invariant 0 <= i <= |s|
      decreases |s| - i
    {
      i := i + 1;
    }
    if i == |s| then
      <s[0..]>
    else
      var rest := Split(s[i+1..], separator);
      var head := s[0..i];
      <head> + rest
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures CorrectOutput(input, result)
ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    var n := ExtractN(input);
    var m := ExtractM(input);
    if n == m then
        result := "Yes";
    else
        result := "No";
}
// </vc-code>

