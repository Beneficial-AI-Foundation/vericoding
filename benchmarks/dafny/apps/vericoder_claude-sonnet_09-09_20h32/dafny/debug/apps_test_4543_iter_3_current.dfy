predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
function IntToString(n: int): string
  requires n >= 0

function StringToInt(s: string): int
  requires |s| > 0

function Sqrt(n: int): int
  requires n >= 0
  ensures Sqrt(n) >= 0
  ensures Sqrt(n) * Sqrt(n) <= n
  ensures (Sqrt(n) + 1) * (Sqrt(n) + 1) > n

lemma ConcatenationProperties(a: int, b: int)
  requires a >= 1 && a <= 100
  requires b >= 1 && b <= 100
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          var concat_num := StringToInt(concat_str);
          concat_num >= 0
{
  var a_str := IntToString(a);
  var b_str := IntToString(b);
  var concat_str := a_str + b_str;
  assert |concat_str| > 0;
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
  
  ConcatenationProperties(a, b);
  
  if IsPerfectSquare(concat_num) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

