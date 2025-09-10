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
function stringToInt(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then s[0] as int - '0' as int
  else 10 * stringToInt(s[..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

function intToString(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0" else intToString(n / 10) + [(n % 10 + 48) as char]
}

function countSpaces(s: string, start: int): int
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start == |s| then 0
  else if s[start] == ' ' then 1 + countSpaces(s, start+1)
  else countSpaces(s, start+1)
}

function findSpaceIndex(s: string): int
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  decreases |s|
{
  if s[0] == ' ' then 0
  else 1 + findSpaceIndex(s[1..])
}

function splitOnSpace(s: string): seq<string>
  requires exists i :: 0 <= i < |s| && s[i] == ' '
{
  var i := findSpaceIndex(s);
  [s[..i], s[i+1..]]
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
  var count := countPalindromicNumbers(a, b);
  result := intToString(count) + "\n";
}
// </vc-code>

