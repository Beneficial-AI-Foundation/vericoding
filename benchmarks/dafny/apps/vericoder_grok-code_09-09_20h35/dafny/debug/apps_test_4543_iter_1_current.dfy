predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
method IsPerfectSquare(n: int) returns (r: bool)
  requires n >= 0
{
  var k := 0;
  while (k * k < n)
  {
    k := k + 1;
  }
  r := k * k == n;
}

function TenPower(k: int): int
  decreases k;
{
  if k == 0 then 1 else 10 * TenPower(k-1);
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

