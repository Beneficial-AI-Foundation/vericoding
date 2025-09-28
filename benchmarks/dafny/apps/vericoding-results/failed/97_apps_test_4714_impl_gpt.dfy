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

function stringToInt(s: string): int

function intToString(n: int): string
  requires n >= 0

axiom (forall n :: n >= 0 ==> isValidInteger(intToString(n)));
axiom (forall n :: n >= 0 ==> stringToInt(intToString(n)) == n);

lemma LemmaAppendNewlineProps(s: string)
  ensures |s + "\n"| > 0
  ensures (s + "\n")[|s + "\n"| - 1] == '\n'
{
  assert |s + "\n"| == |s| + |"\n"|;
  assert |"\n"| == 1;
  assert |s + "\n"| > 0;
  assert |s| < |s + "\n"|;
  assert |s + "\n"| - 1 == |s|;
  assert (s + "\n")[|s|] == "\n"[0];
  assert "\n"[0] == '\n';
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
  assert |parts| == 2;
  var a := stringToInt(parts[0]);
  var b := stringToInt(parts[1]);
  var c := countPalindromicNumbers(a, b);
  assert c >= 0;
  result := intToString(c) + "\n";
  LemmaAppendNewlineProps(intToString(c));
}
// </vc-code>

