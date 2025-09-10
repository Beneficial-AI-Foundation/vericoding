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
  ensures (n == 0) == (|intToString(n)| == 1 && intToString(n)[0] == '0')
  ensures n > 0 ==> intToString(n)[0] != '0'
  ensures (forall i :: 0 <= i < |intToString(n)| ==> '0' <= intToString(n)[i] <= '9')
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant n >= temp
      invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
      invariant n / Power(10, |s|) == temp
      invariant n % Power(10, |s|) == stringToInt(reverseString(s))
      decreases temp
    {
      s := intToDigit(temp % 10) + s;
      temp := temp / 10;
    }
    s
}

function intToDigit(d: int): char
  requires 0 <= d <= 9
  ensures '0' <= intToDigit(d) <= '9'
{
  (d + '0') as char
}

function stringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires s[0] != '0' || |s| == 1
  ensures stringToInt(s) >= 0
{
  var n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
    invariant n == stringToInt_prefix(s, i)
    decreases |s| - i
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  n
}

function stringToInt_prefix(s: string, len: int): int
  requires 0 <= len <= |s|
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires s[0] != '0' || |s| == 1
  ensures stringToInt_prefix(s, len) >= 0
{
  if len == 0 then 0
  else stringToInt(s[..len])
}

function reverseString(s: string): string
{
  var t := "";
  var i := |s| - 1;
  while i >= 0
    invariant -1 <= i < |s|
    invariant t == new string(s[i+1..|s|].Rev())
    decreases i + 1
  {
    t := t + (s[i] as string);
    i := i - 1;
  }
  t
}

function splitOnSpace(s: string): seq<string>
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  ensures forall x :: x in splitOnSpace(s) ==> |x| > 0
{
  var parts: seq<string> := [];
  var start := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant forall k :: 0 <= k < |parts| ==> |parts[k]| > 0
    invariant (i == |s| || s[i] != ' ') ==> (if |parts| == 0 then start == 0 else true)
    invariant (i == |s| || s[i] != ' ') ==> (forall k :: 0 <= k < |parts| ==> (exists j :: 0 <= j < |s| && s[j..j+|parts[k]|] == parts[k]))
    decreases |s| - i
  {
    if s[i] == ' '
    {
      if i > start
      {
        parts := parts + [s[start..i]];
      }
      start := i + 1;
    }
    i := i + 1;
  }
  if i > start
  {
    parts := parts + [s[start..i]];
  }
  parts
}

function NumberOfDigits(n: int): int
  requires n >= 0
  ensures NumberOfDigits(n) >= 1
  ensures n == 0 ==> NumberOfDigits(n) == 1
{
  if n == 0 then 1
  else
    var count := 0;
    var temp := n;
    while temp > 0
      invariant temp >= 0
      decreases temp
    {
      temp := temp / 10;
      count := count + 1;
    }
    count
}

function Power(base: int, exponent: int): int
  requires exponent >= 0
  ensures Power(base, exponent) >= 0
{
  if exponent == 0 then 1
  else base * Power(base, exponent - 1)
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

