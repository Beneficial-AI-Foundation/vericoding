Count the number of palindromic numbers in the range [A, B] inclusive.
A palindromic number is a positive integer that reads the same forwards and backwards when written in decimal notation.
Constraints: 10000 ≤ A ≤ B ≤ 99999

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

function splitOnSpace(s: string): seq<string>
  requires exists i :: 0 <= i < |s| && s[i] == ' '
{
  var spaceIndex := findSpace(s, 0);
  if spaceIndex == -1 then []
  else [s[..spaceIndex], trim(s[spaceIndex+1..])]
}

function findSpace(s: string, start: int): int
  requires 0 <= start <= |s|
  ensures findSpace(s, start) == -1 || (start <= findSpace(s, start) < |s| && s[findSpace(s, start)] == ' ')
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == ' ' then start
  else findSpace(s, start + 1)
}

function trim(s: string): string
{
  if |s| == 0 then s
  else if s[|s|-1] == '\n' then s[..|s|-1]
  else s
}

function stringToInt(s: string): int
  requires isValidInteger(s)
  ensures stringToInt(s) >= 0
  decreases |s|
{
  if |s| == 0 then 0
  else if |s| == 1 then s[0] as int - '0' as int
  else 
    assert isValidInteger(s[..|s|-1]);
    stringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function intToString(n: int): string
  requires n >= 0
  ensures |intToString(n)| > 0
  ensures n == 0 ==> intToString(n) == "0"
  ensures n > 0 ==> forall i :: 0 <= i < |intToString(n)| ==> '0' <= intToString(n)[i] <= '9'
  decreases n
{
  if n == 0 then "0"
  else if n < 10 then [('0' as int + n) as char]
  else intToString(n / 10) + [('0' as int + (n % 10)) as char]
}

method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures var parts := splitOnSpace(stdin_input);
          var a := stringToInt(parts[0]);
          var b := stringToInt(parts[1]);
          result == intToString(countPalindromicNumbers(a, b)) + "\n"
{
  var parts := splitOnSpace(stdin_input);
  var a := stringToInt(parts[0]);
  var b := stringToInt(parts[1]);
  var count := countPalindromicNumbers(a, b);
  result := intToString(count) + "\n";
}
