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
lemma SplitFirstLineParts(input: string)
requires ValidInput(input)
ensures |SplitString(SplitString(input, '\n')[0], ' ')| == 2
{
}

lemma StringToIntProperties(input: string)
requires ValidInput(input)
ensures var lines := SplitString(input, '\n');
         var parts := SplitString(lines[0], ' ');
         var n := StringToInt(parts[0]);
         var m := StringToInt(parts[1]);
         1 <= n <= 100 && 0 <= m <= n
{
}

function SplitString(s: string, sep: char): seq<string>
{
  if |s| == 0 then []
  else if s[0] == sep then [""] + SplitString(s[1..], sep)
  else
    var rest := SplitString(s[1..], sep);
    [rest[0] + [s[0]]] + rest[1..]
}

function StringToInt(s: string): int
{
  if |s| == 0 then 0
  else (s[|s|-1] as int - '0' as int) + 10 * StringToInt(s[..|s|-1])
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists lines :: lines == SplitString(input, '\n') && |lines| > 0 &&
    exists parts :: parts == SplitString(lines[0], ' ') && |parts| == 2 &&
    exists n, m :: n == StringToInt(parts[0]) && 
                   m == StringToInt(parts[1]) &&
                   1 <= n <= 100 && 0 <= m <= n
}

function ExtractN(input: string): int
requires ValidInput(input)
{
    var lines := SplitString(input, '\n');
    var parts := SplitString(lines[0], ' ');
    StringToInt(parts[0])
}

function ExtractM(input: string): int
requires ValidInput(input)
{
    var lines := SplitString(input, '\n');
    var parts := SplitString(lines[0], ' ');
    StringToInt(parts[1])
}

predicate CorrectOutput(input: string, result: string)
requires ValidInput(input)
{
    var n := ExtractN(input);
    var m := ExtractM(input);
    (n == m ==> result == "Yes") && (n != m ==> result == "No")
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
  var lines := SplitString(input, '\n');
  var parts := SplitString(lines[0], ' ');
  var n := StringToInt(parts[0]);
  var m := StringToInt(parts[1]);
  
  if n == m {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

