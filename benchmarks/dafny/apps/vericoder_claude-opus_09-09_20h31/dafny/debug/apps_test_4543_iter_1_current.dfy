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

function IntToString(n: int): string
  requires n >= 0
  ensures StringToInt(IntToString(n)) == n
  ensures |IntToString(n)| >= 1

function StringToInt(s: string): int
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0

lemma IntToStringDigits(n: int)
  requires n >= 0
  ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'

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
  
  IntToStringDigits(a);
  IntToStringDigits(b);
  ConcatPreservesDigits(a_str, b_str);
  
  var concat_num := StringToInt(concat_str);
  
  if IsPerfectSquare(concat_num) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

