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
function TrimNewline(s: string): string {
  if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s
}

function FindChar(s: string, c: char, start: int): int
  decreases |s| - start
{
  if start < 0 || start >= |s| then -1
  else if s[start] == c then start
  else FindChar(s, c, start+1)
}

function SplitByChar(s: string, c: char): seq<string>
  decreases |s|
{
  if s == "" then []
  else
    var i := FindChar(s, c, 0);
    if i < 0 then [s]
    else if i == |s|-1 then [s[..i]] + [""]
    else [s[..i]] + SplitByChar(s[i+1..], c)
}

function Filter<T>(s: seq<T>, p: T -> bool): seq<T>
  decreases s
{
  if |s| == 0 then []
  else if p(s[0]) then [s[0]] + Filter(s[1..], p)
  else Filter(s[1..], p)
}

function SplitSpaces(s: string): seq<string> {
  var tokens := SplitByChar(s, ' ');
  Filter(tokens, t => t != "")
}

function StringToInt(s: string): int

function IntToString(i: int): string
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
  var meals := CalculateMissedMeals(input);
  result := IntToString(meals);
}
// </vc-code>

