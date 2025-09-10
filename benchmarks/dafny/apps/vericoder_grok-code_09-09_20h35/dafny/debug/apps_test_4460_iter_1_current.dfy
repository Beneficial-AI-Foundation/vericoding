predicate validInput(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

predicate validNumber(s: string)
{
    |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function countZeros(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else (if numbers[0] == 0 then 1 else 0) + countZeros(numbers[1..])
}

function findZeroIndex(numbers: seq<int>): int
    requires |numbers| > 0
    requires countZeros(numbers) == 1
{
    if numbers[0] == 0 then 0
    else if |numbers| > 1 then 1 + findZeroIndex(numbers[1..])
    else 0
}

function parseInts(s: string): seq<int>
    requires |s| > 0
    requires validInput(s)
{
    parseIntsHelper(s, 0, "", [])
}

function generateOutput(numbers: seq<int>): string
{
    generateOutputHelper(numbers, 0, "")
}

// <vc-helpers>
function power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

function parsePosInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then s[0] as int - '0' as int
  else((s[0] as int - '0' as int) * power(10, |s| - 1)) + parsePosInt(s[1..])
}

function parseInt(s: string): int
  requires |s| > 0
  requires validNumber(s)
{
  if s[0] == '-' then -parsePosInt(s[1..]) else parsePosInt(s)
}

function parseIntsHelper(s: string, pos: int, num: string, numbers: seq<int>): seq<int>
  requires 0 <= pos <= |s|
  requires validInput(s)
  requires |num| == 0 || validNumber(num)
  decreases |s| - pos
{
  if pos == |s| then
    if |num| > 0 then numbers + [parseInt(num)] else numbers
  else
    var c := s[pos];
    if c == ' ' || c == '\n' then
      if |num| > 0 then
        parseIntsHelper(s, pos + 1, "", numbers + [parseInt(num)])
      else
        parseIntsHelper(s, pos + 1, "", numbers)
    else
      parseIntsHelper(s, pos + 1, num + [c], numbers)
}

function digits(i: int): string
  requires i > 0
  decreases i
{
  if i < 10 then [((i + '0' as int) as char)] else digits(i / 10) + [((i % 10 + '0' as int) as char)]
}

function intToString(i: int): string
{
  if i < 0 then "-" + intToString(-i) else if i == 0 then "0" else digits(i)
}

function generateOutputHelper(numbers: seq<int>, idx: int, accum: string): string
  requires 0 <= idx <= |numbers|
  decreases |numbers| - idx
{
  if idx == |numbers| then accum
  else if idx == 0 then
    generateOutputHelper(numbers, idx + 1, accum + intToString(numbers[idx]))
  else
    generateOutputHelper(numbers, idx + 1, accum + " " + intToString(numbers[idx]))
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires validInput(input)
    requires |input| > 0
    ensures var numbers := parseInts(input);
            result == generateOutput(numbers)
// </vc-spec>
// <vc-code>
{
  result := generateOutput(parseInts(input));
}
// </vc-code>

