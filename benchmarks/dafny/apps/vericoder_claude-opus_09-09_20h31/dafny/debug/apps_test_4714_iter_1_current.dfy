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
function splitOnSpace(s: string): seq<string>
  ensures |splitOnSpace(s)| >= 1
{
  if |s| == 0 then [""]
  else if exists i :: 0 <= i < |s| && s[i] == ' ' then
    var i :| 0 <= i < |s| && s[i] == ' ';
    [s[..i]] + splitOnSpace(s[i+1..])
  else [s]
}

function stringToInt(s: string): int
  requires isValidInteger(s)
  ensures stringToInt(s) >= 0
{
  if |s| == 1 then (s[0] - '0') as int
  else stringToInt(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as int
}

function intToString(n: int): string
  requires n >= 0
  ensures isValidInteger(intToString(n))
  ensures stringToInt(intToString(n)) == n
  decreases n
{
  if n < 10 then [(n + '0' as int) as char]
  else intToString(n / 10) + [(n % 10 + '0' as int) as char]
}

method computeCountPalindromicNumbers(a: int, b: int) returns (count: int)
  requires 10000 <= a <= b <= 99999
  ensures count == countPalindromicNumbers(a, b)
  decreases b - a + 1
{
  if a > b {
    count := 0;
  } else if a == b {
    if isPalindromic(a) {
      count := 1;
    } else {
      count := 0;
    }
  } else {
    var rest := computeCountPalindromicNumbers(a + 1, b);
    if isPalindromic(a) {
      count := 1 + rest;
    } else {
      count := rest;
    }
  }
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
  var count := computeCountPalindromicNumbers(a, b);
  result := intToString(count) + "\n";
}
// </vc-code>

