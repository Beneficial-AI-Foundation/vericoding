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
function intToString(n: int): string
  requires n >= 0
  ensures |result| > 0
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
  if n < 10 then [(('0' as int) + n) as char]
  else intToString(n / 10) + [(('0' as int) + (n % 10)) as char]
}

function stringToInt(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures result >= 0
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else 10 * stringToInt(s[0..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function splitOnSpace(s: string): (string, string)
  requires |s| > 0 && exists i :: 0 <= i < |s| && s[i] == ' '
  ensures var (p1, p2) := result; |p1| > 0 && |p2| > 0 && exists i :: 0 <= i < |s| && s[i] == ' ' && p1 == s[0..i] && p2 == s[i+1..]
{
  var i :| 0 <= i < |s| && s[i] == ' ';
  (s[0..i], s[i+1..])
}

lemma splitOnSpaceLemma(s: string)
  requires |s| > 0 && exists i :: 0 <= i < |s| && s[i] == ' '
  ensures var (p1, p2) := splitOnSpace(s); |p1| > 0 && |p2| > 0
{
  var i :| 0 <= i < |s| && s[i] == ' ';
  assert |s[0..i]| == i;
  if i == 0 {
    // This case cannot happen because |s| > 0 and i == 0 would mean we skip the first character
    assert false;
  }
  if i == |s| - 1 {
    // This case cannot happen because we wouldn't have any characters after space
    assert false;
  }
  assert i > 0;
  assert |s| - i - 1 > 0;
}

lemma stringToIntValid(s: string)
  requires isValidInteger(s)
  ensures stringToInt(s) >= 0
{
}

lemma countPalindromicNumbersRange(a: int, b: int)
  requires 10000 <= a <= b <= 99999
  ensures 0 <= countPalindromicNumbers(a, b) <= b - a + 1
{
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
  var i :| 0 <= i < |stdin_input| && stdin_input[i] == ' ';
  var p0 := stdin_input[0..i];
  var p1 := stdin_input[i+1..];
  assert isValidInteger(p0);
  assert isValidInteger(p1);
  var a := stringToInt(p0);
  var b := stringToInt(p1);
  var count := countPalindromicNumbers(a, b);
  result := intToString(count) + "\n";
}
// </vc-code>

