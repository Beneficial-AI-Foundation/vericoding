predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
function Sqrt(n: int): int
  requires n >= 0
  decreases n
  ensures 0 <= Sqrt(n) && Sqrt(n) * Sqrt(n) <= n && n < (Sqrt(n) + 1) * (Sqrt(n) + 1)
{
  if n == 0 then 0
  else
    let r := Sqrt(n - 1) in
      if (r + 1) * (r + 1) <= n then r + 1 else r
}

function IntToString(x: int): string

function StringToInt(s: string): int
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
  if IsPerfectSquare(concat_num) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

