function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}

// <vc-helpers>
lemma Max3Properties(a: int, b: int, c: int)
ensures Max3(a, b, c) >= a
ensures Max3(a, b, c) >= b
ensures Max3(a, b, c) >= c
ensures Max3(a, b, c) == a || Max3(a, b, c) == b || Max3(a, b, c) == c
{}
function IsDigit(c: char): bool
{
  '0' <= c <= '9'
}
function TrimNewline(s: string): string
{
  if |s| > 0 && (s[|s|-1] == '\n' || s[|s|-1] == '\r') then TrimNewline(s[..|s|-1])
  else s
}
function FindWordEnd(s: string, start: int): int
{
  if start >= |s| || s[start] == ' ' then start
  else FindWordEnd(s, start + 1)
}
function SplitSpacesAux(s: string, pos: int): seq<string>
decreases |s| - pos
{
  if pos >= |s| then []
  else if s[pos] == ' ' then SplitSpacesAux(s, pos + 1)
  else 
    var end := FindWordEnd(s, pos);
    [s[pos..end]] + SplitSpacesAux(s, end)
}
function SplitSpaces(s: string): seq<string>
{
  SplitSpacesAux(s, 0)
}
function StringToInt(s: string): int
decreases |s|
{
  if |s| == 0 then 0
  else if IsDigit(s[0]) then (s[0] as int - '0' as int) + 10 * StringToInt(s[1..])
  else 0
}
function IntToString(i: int): string
requires i >= 0
decreases i
{
  if i == 0 then "0"
  else IntToString(i / 10) + [i % 10 + '0' as int as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
  var val := CalculateMissedMeals(input);
  result := IntToString(val);
}
// </vc-code>

