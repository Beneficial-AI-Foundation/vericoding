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
function findFirstSpace(s: string): nat
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  ensures 0 <= findFirstSpace(s) < |s| && s[findFirstSpace(s)] == ' '
  ensures forall j :: 0 <= j < findFirstSpace(s) ==> s[j] != ' '
{
  var spaceIndex :| 0 <= spaceIndex < |s| && s[spaceIndex] == ' ' && 
                   forall j :: 0 <= j < spaceIndex ==> s[j] != ' ';
  spaceIndex
}

function splitOnSpace(s: string): seq<string>
  requires exists i :: 0 <= i < |s| && s[i] == ' '
{
  var spaceIndex := findFirstSpace(s);
  [s[0..spaceIndex], s[spaceIndex+1..]]
}

function stringToIntRecursive(s: string, acc: int): int
  requires isValidInteger(s)
  decreases |s|
{
  if |s| == 0 then acc
  else stringToIntRecursive(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function stringToInt(s: string): int
  requires isValidInteger(s)
{
  stringToIntRecursive(s, 0)
}

function intToStringRecursive(n: int, suffix: string): string
  requires n > 0
  decreases n
{
  if n < 10 then [(n as int + '0' as int) as char] + suffix
  else intToStringRecursive(n / 10, [(n % 10 as int + '0' as int) as char] + suffix)
}

function intToString(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else intToStringRecursive(n, "")
}

lemma ValidInputProperties(s: string)
  requires ValidInput(s)
  ensures |splitOnSpace(s)| == 2
  ensures isValidInteger(splitOnSpace(s)[0])
  ensures isValidInteger(splitOnSpace(s)[1])
  ensures stringToInt(splitOnSpace(s)[0]) >= 10000
  ensures stringToInt(splitOnSpace(s)[0]) <= 99999
  ensures stringToInt(splitOnSpace(s)[1]) >= 10000
  ensures stringToInt(splitOnSpace(s)[1]) <= 99999
  ensures stringToInt(splitOnSpace(s)[0]) <= stringToInt(splitOnSpace(s)[1])
{
  reveal ValidInput();
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
  ValidInputProperties(stdin_input);
  var parts := splitOnSpace(stdin_input);
  var a := stringToInt(parts[0]);
  var b := stringToInt(parts[1]);
  var count := countPalindromicNumbers(a, b);
  result := intToString(count) + "\n";
}
// </vc-code>

