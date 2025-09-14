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
function FindDelimiter(s: string, delimiter: char, start: int): int
requires 0 <= start <= |s|
decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == delimiter then start
    else FindDelimiter(s, delimiter, start + 1)
}

function Split(s: string, delimiter: char): seq<string>
{
    if s == "" then []
    else
        var index := FindDelimiter(s, delimiter, 0);
        if index == |s| then [s]
        else [s[..index]] + Split(s[index+1..], delimiter)
}

function StringToInt(s: string): int
requires |s| > 0
decreases |s|
{
    if |s| == 1 then
        if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0
    else
        10 * StringToInt(s[..|s|-1]) + (if '0' <= s[|s|-1] <= '9' then (s[|s|-1] as int) - ('0' as int) else 0)
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
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

