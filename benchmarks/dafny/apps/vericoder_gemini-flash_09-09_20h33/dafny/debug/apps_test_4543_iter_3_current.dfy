predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
function Sqrt(n: int): (root: int)
  requires n >= 0
  ensures root * root <= n < (root + 1) * (root + 1)
{
  if n == 0 then 0
  else if n == 1 then 1
  else
    var low := 0;
    var high := n;
    var result := 0;
    while low <= high
      invariant 0 <= low <= n + 1
      invariant -1 <= high <= n
      invariant low <= high + 1
      invariant result * result <= n
      invariant (low == 0 && high == n) ==> result == 0
      invariant result * result <= n
      invariant high < low ==> result * result <= n < (result + 1) * (result + 1)
      invariant low <= high ==> low * low <= n || high * high >= n || low == 0 || high == 0
      invariant low <= high ==> result == 0 || (result + 1) * (result + 1) > n
      invariant low <= high ==> result <= low || low == 0
      invariant low <= high ==> result <= high + 1 // Corrected invariant
      invariant low <= high ==> (result +1) * (result + 1) > (low - 1) * (low - 1) || low == 0
    {
      var mid := low + (high - low) / 2;
      if mid * mid == n then
        return mid
      else if mid * mid < n then
        result := mid;
        low := mid + 1;
      else
        high := mid - 1;
    }
    result
}

// Function to convert an integer to a string (base 10)
function IntToString(n: int): string
  requires n >= 0
  ensures (n == 0 ==> this == "0")
  ensures (n > 0 ==> var num := n; var s := "";
            while num > 0
              invariant num >= 0
              invariant (var p := Power(10, |s|); n / p == num)
              invariant (var p_s := StringToInt(s); p_s < Power(10, |s|) || s == "")
            {
              s := ((num % 10) as char + '0') + s;
              num := num / 10;
            }
            this == s)
{
  if n == 0 then "0"
  else
    var s := "";
    var num := n;
    while num > 0
      invariant num >= 0
      invariant (var p := Power(10, |s|); n / p == num)
      invariant (var p_s := StringToInt(s); p_s < Power(10, |s|) || s == "")
    {
      s := ((num % 10) as char + '0') + s; // Corrected char conversion
      num := num / 10;
    }
    s
}

// Function to convert a character (digit) to an integer
function CharToInt(c: char): int
  requires '0' <= c <= '9'
  ensures 0 <= this <= 9
{
  c as int - '0' as int
}

// Function to convert a string of digits to an integer
function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
  ensures this >= 0
  ensures StringToInt_Correct(s, this)

function StringToInt_Correct(s: string, res: int): bool
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
{
  var num_str := IntToString(res);
  num_str == s
}


{
  var result := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant (i == 0 ==> result == 0)
    invariant (i > 0 ==> result == StringToInt(s[..i]))
  {
    if i < |s| {
      result := result * 10 + CharToInt(s[i]);
    }
  }
  return result;
}

function Power(base: int, exp: int): int
  requires exp >= 0
  requires base >= 0
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
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
  var concat_num := StringToInt(concat_str);

  if IsPerfectSquare(concat_num) then
    result := "Yes";
  else
    result := "No";
  return result;
}
// </vc-code>

