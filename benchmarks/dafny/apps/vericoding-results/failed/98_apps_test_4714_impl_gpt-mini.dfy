predicate isPalindromic(n: int)
  requires n >= 0
{
  var s := intToString(n);
  forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

function countPalindromicNumbers(a: int, b: int): int
  requires 10000 <= a <= b <= 99999
  ensures countPalindromicNumbers(a, b) >= 0
  ensures countPalindromicNumbers(a, b) <= b - a + 1
  decreases b - a + 1
{
  if a > b then 0
  else if a == b then (if isPalindromic(a) then 1 else 0)
  else (if isPalindromic(a) then 1 else 0) + countPalindromicNumbers(a + 1, b)
}

predicate isValidInteger(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate ValidInput(stdin_input: string)
{
  |stdin_input| > 0 &&
  exists i :: 0 <= i < |stdin_input| && stdin_input[i] == ' ' &&
  var parts := splitOnSpace(stdin_input);
  |parts| == 2 && 
  isValidInteger(parts[0]) && 
  isValidInteger(parts[1]) &&
  stringToInt(parts[0]) >= 10000 &&
  stringToInt(parts[1]) >= 10000 &&
  stringToInt(parts[0]) <= 99999 &&
  stringToInt(parts[1]) <= 99999 &&
  stringToInt(parts[0]) <= stringToInt(parts[1])
}

// <vc-helpers>
function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function digitValue(c: char): int
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
  else 9
}

function digitChar(d: int): string
  requires 0 <= d <= 9
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}

function indexFirstSpace(s: string): int
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  decreases |s|
  ensures 0 <= result < |s|
  ensures s[result] == ' '
{
  if s[0] == ' ' then 0 else 1 + indexFirstSpace(s[1..])
}

function splitOnSpace(s: string): seq<string>
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  ensures |result| == 2
  ensures result[0] == s[..indexFirstSpace(s)]
  ensures result[1] == s[indexFirstSpace(s) + 1..]
{
  var i := indexFirstSpace(s);
  [s[..i], s[i + 1..]]
}

function stringToInt(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then digitValue(s[0])
  else digitValue(s[0]) * pow10(|s| - 1) + stringToInt(s[1..])
}

function intToString(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0"
  else if n < 10 then digitChar(n)
  else intToString(n / 10) + digitChar(n % 10)
}

predicate isValidInteger(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate ValidInput(stdin_input: string)
{
  |stdin_input| > 0 &&
  exists i :: 0 <= i < |stdin_input| && stdin_input[i] == ' ' &&
  let parts := splitOnSpace(stdin_input) in
    |parts| == 2 &&
    isValidInteger(parts[0]) &&
    isValidInteger(parts[1]) &&
    stringToInt(parts[0]) >= 10000 &&
    stringToInt(parts[1]) >= 10000 &&
    stringToInt(parts[0]) <= 99999 &&
    stringToInt(parts[1]) <= 99999 &&
    stringToInt(parts[0]) <= stringToInt(parts[1])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures var parts := splitOnSpace(stdin_input);
          var a := stringToInt(parts[0]);
          var b := stringToInt(parts[1]);
          result == intToString(countPalindromicNumbers(a, b)) + "\n"
// </vc-spec>
// <vc-code>
{
  var parts := splitOnSpace(stdin_input);
  var a := stringToInt(parts[0]);
  var b := stringToInt(parts[1]);
  result := intToString(countPalindromicNumbers(a, b)) + "\n";
}
// </vc-code>

