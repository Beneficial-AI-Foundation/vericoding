predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
function Sqrt(n: int): int
  requires n >= 0
  ensures Sqrt(n) >= 0
  ensures Sqrt(n) * Sqrt(n) <= n < (Sqrt(n) + 1) * (Sqrt(n) + 1)
{
  if n == 0 then 0
  else SqrtHelper(n, 0, n + 1)
}

function SqrtHelper(n: int, low: int, high: int): int
  requires n > 0
  requires 0 <= low < high
  requires low * low <= n
  requires n < high * high
  ensures low <= SqrtHelper(n, low, high) < high
  ensures SqrtHelper(n, low, high) * SqrtHelper(n, low, high) <= n < (SqrtHelper(n, low, high) + 1) * (SqrtHelper(n, low, high) + 1)
  decreases high - low
{
  if low + 1 == high then
    low
  else
    var mid := (low + high) / 2;
    if mid * mid <= n then
      SqrtHelper(n, mid, high)
    else
      SqrtHelper(n, low, mid)
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| >= 1
  ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
  if n == 0 then "0"
  else if n < 10 then [('0' as char) + (n as char)]
  else IntToString(n / 10) + [('0' as char) + ((n % 10) as char)]
}

function StringToInt(s: string): int
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

lemma IntToStringInverse(n: int)
  requires n >= 0
  ensures StringToInt(IntToString(n)) == n
{
  // This lemma establishes the inverse relationship
}

lemma ConcatPreservesDigits(a_str: string, b_str: string)
  requires forall i :: 0 <= i < |a_str| ==> '0' <= a_str[i] <= '9'
  requires forall i :: 0 <= i < |b_str| ==> '0' <= b_str[i] <= '9'
  ensures forall i :: 0 <= i < |a_str + b_str| ==> '0' <= (a_str + b_str)[i] <= '9'
{
  var concat_str := a_str + b_str;
  forall i | 0 <= i < |concat_str|
    ensures '0' <= concat_str[i] <= '9'
  {
    if i < |a_str| {
      assert concat_str[i] == a_str[i];
    } else {
      assert concat_str[i] == b_str[i - |a_str|];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires a >= 1 && a <= 100
  requires b >= 1 && b <= 100
  ensures result == "Yes" || result == "No"
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          var concat_num := StringToInt(concat_str);
          result == "Yes" <==> IsPerfectSquare(concat_num)
// </vc-spec>
// <vc-code>
{
  var a_str := IntToString(a);
  var b_str := IntToString(b);
  var concat_str := a_str + b_str;
  
  ConcatPreservesDigits(a_str, b_str);
  
  var concat_num := StringToInt(concat_str);
  
  IntToStringInverse(a);
  IntToStringInverse(b);
  
  if IsPerfectSquare(concat_num) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

