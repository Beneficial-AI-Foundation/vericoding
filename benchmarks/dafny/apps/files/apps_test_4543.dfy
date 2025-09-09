Given two positive integers a and b, determine whether their string concatenation 
(a followed by b) forms a perfect square number. Return "Yes" if it's a perfect 
square, "No" otherwise.

predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| > 0
  ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
  if n == 0 then "0"
  else if n < 10 then [('0' as int + n) as char]
  else IntToString(n / 10) + IntToString(n % 10)
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function Sqrt(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else SqrtHelper(n, 0, n)
}

function SqrtHelper(n: int, low: int, high: int): int
  requires n >= 0
  requires low >= 0
  requires high >= 0
  requires low <= high
  decreases high - low
{
  if low == high then low
  else if low + 1 == high then
    if high * high <= n then high else low
  else
    var mid := (low + high) / 2;
    if mid * mid <= n then SqrtHelper(n, mid, high)
    else SqrtHelper(n, low, mid - 1)
}

lemma ConcatDigitStrings(s1: string, s2: string)
  requires |s1| > 0 && |s2| > 0
  requires forall i :: 0 <= i < |s1| ==> '0' <= s1[i] <= '9'
  requires forall i :: 0 <= i < |s2| ==> '0' <= s2[i] <= '9'
  ensures |s1 + s2| > 0
  ensures forall i :: 0 <= i < |s1 + s2| ==> '0' <= (s1 + s2)[i] <= '9'
{
}

method solve(a: int, b: int) returns (result: string)
  requires a >= 1 && a <= 100
  requires b >= 1 && b <= 100
  ensures result == "Yes" || result == "No"
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          var concat_num := StringToInt(concat_str);
          result == "Yes" <==> IsPerfectSquare(concat_num)
{
  var a_str := IntToString(a);
  var b_str := IntToString(b);
  var concat_str := a_str + b_str;

  ConcatDigitStrings(a_str, b_str);

  var concat_num := StringToInt(concat_str);

  if IsPerfectSquare(concat_num) {
    result := "Yes";
  } else {
    result := "No";
  }
}
