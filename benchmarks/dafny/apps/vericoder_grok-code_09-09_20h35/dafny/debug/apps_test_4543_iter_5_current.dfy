predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  exists k : int :: k >= 0 && k*k == n
}

function TenPower(k: int): int
  requires k >= 0
  decreases k
{
  if k == 0 then 1 else 10 * TenPower(k-1)
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString| > 0
  ensures forall i :: 0 <= i < |IntToString| ==> '0' <= IntToString[i] <= '9'
  decreases n
{
  if n == 0 then "0"
  else
    IntToString(n / 10) + [((n % 10) + 48) as? char]
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt >= 0
  ensures IntToString(StringToInt) == s
  decreases |s|
{
  if |s| == 1 then s[0] as? int - 48
  else 10 * StringToInt(s[..|s|-1]) + (s[|s|-1] as? int - 48)
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
  var len_b := if b <=9 then 1 else if b < 100 then 2 else 3;
  var power10 := TenPower(len_b);
  var concat_num := a * power10 + b;
  var is_square := IsPerfectSquare(concat_num);
  result := if is_square then "Yes" else "No";
}
// </vc-code>

