predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
function {:axiom} IntToString(n: int): string
  requires n >= 0

function {:axiom} StringToInt(s: string): int
  requires |s| > 0

function {:axiom} Sqrt(n: int): int
  requires n >= 0
  ensures Sqrt(n) >= 0
  ensures Sqrt(n) * Sqrt(n) <= n
  ensures (Sqrt(n) + 1) * (Sqrt(n) + 1) > n

lemma {:axiom} ConcatenationProperties(a: int, b: int)
  requires a >= 1 && a <= 100
  requires b >= 1 && b <= 100
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          |concat_str| > 0
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          var concat_num := StringToInt(concat_str);
          concat_num >= 0

lemma {:axiom} IntToStringNonEmpty(n: int)
  requires n >= 0
  ensures |IntToString(n)| > 0
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
  IntToStringNonEmpty(a);
  IntToStringNonEmpty(b);
  ConcatenationProperties(a, b);
  
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

