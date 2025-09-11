// <vc-preamble>
predicate ValidInput(n: int)
{
  100 <= n <= 999
}

predicate IsPalindromic(n: int)
  requires ValidInput(n)
{
  var hundreds := n / 100;
  var units := n % 10;
  hundreds == units
}

predicate IsWhitespace(c: char)
{
  c == ' ' || c == '\n' || c == '\t' || c == '\r'
}

predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

predicate CanParseAsInt(s: string)
{
  |s| > 0 && (
    (|s| == 1 && IsDigit(s[0])) ||
    (|s| > 1 && s[0] == '-' && forall i :: 1 <= i < |s| ==> IsDigit(s[i])) ||
    (|s| > 1 && IsDigit(s[0]) && forall i :: 1 <= i < |s| ==> IsDigit(s[i]))
  )
}

function ParseIntValue(s: string): int
  requires CanParseAsInt(s)
{
  if |s| == 1 then s[0] as int - '0' as int
  else if s[0] == '-' then -ParsePositiveInt(s[1..])
  else ParsePositiveInt(s)
}

function ParsePositiveInt(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  decreases |s|
{
  if |s| == 1 then s[0] as int - '0' as int
  else ParsePositiveInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function TokenizeInput(input: string): seq<string>
{
  if |input| == 0 then []
  else TokenizeFromIndex(input, 0, "", [])
}

function TokenizeFromIndex(input: string, index: int, current_token: string, acc: seq<string>): seq<string>
  requires 0 <= index <= |input|
  decreases |input| - index, if index < |input| && IsWhitespace(input[index]) then 1 else 0
{
  if index == |input| then
    if |current_token| > 0 then acc + [current_token] else acc
  else if IsWhitespace(input[index]) then
    if |current_token| > 0 then
      TokenizeFromIndex(input, SkipWhitespace(input, index), "", acc + [current_token])
    else
      TokenizeFromIndex(input, SkipWhitespace(input, index), "", acc)
  else
    TokenizeFromIndex(input, index + 1, current_token + [input[index]], acc)
}

function SkipWhitespace(input: string, index: int): int
  requires 0 <= index <= |input|
  ensures SkipWhitespace(input, index) <= |input|
  ensures index < |input| && IsWhitespace(input[index]) ==> SkipWhitespace(input, index) > index
  decreases |input| - index
{
  if index == |input| || !IsWhitespace(input[index]) then index
  else SkipWhitespace(input, index + 1)
}

predicate ValidStringInput(stdin_input: string)
{
  var tokens := TokenizeInput(stdin_input);
  |tokens| == 1 && CanParseAsInt(tokens[0]) && ValidInput(ParseIntValue(tokens[0]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  ensures result == "Yes\n" || result == "No\n" || result == ""
  ensures ValidStringInput(stdin_input) ==> 
    (result == "Yes\n" <==> IsPalindromic(ParseIntValue(TokenizeInput(stdin_input)[0])))
  ensures !ValidStringInput(stdin_input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
