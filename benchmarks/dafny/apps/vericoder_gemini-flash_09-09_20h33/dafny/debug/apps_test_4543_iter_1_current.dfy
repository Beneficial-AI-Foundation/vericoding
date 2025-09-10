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
      invariant 0 <= low <= high + 1
      invariant result * result <= n
      invariant low == 0 ==> result == 0
      invariant high == n ==> high >= 0
      invariant result <= high
      invariant result <= low
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
  ensures (var num_str := "0"; n == 0 ==> this == num_str)
  ensures (n > 0 ==> var num := n; var s := "";
            while num > 0
              invariant num >= 0
              invariant (var p := Power(10, |s|); n / p == num)
              invariant (var p_s := StringToInt(s); p_s < Power(10, |s|)) // s is a valid representation of a number less than Power(10, |s|)
            {
              s := (num % 10 as char) + s;
              num := num / 10;
            }
            this == s)
{
  if n == 0 then "0"
  else
    var s := "";
    var num := n;
    while num > 0
      ensures num >= 0
      ensures (var p := Power(10, |s|); n / p == num)
      ensures (var p_s := StringToInt(s); p_s < Power(10, |s|))
    {
      s := ((num % 10) as char) + s;
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
  ensures (var num_str := IntToString(this); num_str == s)
{
  var result := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant (var sub_s := s[..i];
                var current_val := 0;
                if |sub_s| > 0 then
                  for k := 0 to |sub_s|-1
                    invariant 0 <= k <= |sub_s|
                    invariant current_val == (if k == 0 then 0 else StringToInt(sub_s[..k]))
                  {
                    current_val := current_val * 10 + CharToInt(sub_s[k]);
                  }
                  result == current_val
                else result == 0)
  {
    result := result * 10 + CharToInt(s[i]);
  }
  result
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

