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
function IndexOf(s: string, c: char): int
  decreases |s|
  ensures IndexOf(s, c) == -1 || 0 <= IndexOf(s, c) < |s|
  ensures IndexOf(s, c) >= 0 ==> s[IndexOf(s, c)] == c
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else
    var i := IndexOf(s[1..], c);
    if i == -1 then -1 else i + 1
}

function Split(s: string, sep: char): seq<string>
  ensures |Split(s, sep)| == 2
{
  var k := IndexOf(s, sep);
  if k < 0 then [s, ""] else [s[..k], s[k+1..]]
}

function DigitVal(c: char): int
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else if c == '9' then 9
  else 0
}

function StringToNat(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else 10 * StringToNat(s[..|s|-1]) + DigitVal(s[|s|-1])
}

function StringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == '-' then -StringToNat(s[1..])
  else StringToNat(s)
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
  if n == m {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

