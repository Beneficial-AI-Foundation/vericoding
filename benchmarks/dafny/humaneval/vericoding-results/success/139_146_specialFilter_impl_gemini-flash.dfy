// <vc-preamble>
function first_digit(n: int): int
  requires n >= 0
  ensures 0 <= first_digit(n) < 10
{
  if n < 10 then n else first_digit(n / 10)
}
function last_digit(n: int): int
  requires n >= 0
  ensures 0 <= last_digit(n) < 10
  ensures last_digit(n) == n % 10
{
  n % 10
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the 'n >= 0' requires clause from IsSpecial function */
function IsSpecial(n: int): bool
  ensures IsSpecial(n) == (n > 10 && first_digit(n) % 2 == 1 && last_digit(n) % 2 == 1)
{
  n > 10 && first_digit(n) % 2 == 1 && last_digit(n) % 2 == 1
}
// </vc-helpers>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)

  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added precondition for IsSpecial function in loop invariant */
{
  var temp_r: seq<int> := [];
  if |s| > 0 {
    for i := 0 to |s| - 1 
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |temp_r| ==> temp_r[j] >= 0 && IsSpecial(temp_r[j]) && temp_r[j] in s
    {
      var x := s[i];
      if x >= 0 && IsSpecial(x) {
        temp_r := temp_r + [x];
      }
    }
  }
  r := temp_r;
}
// </vc-code>
