// <vc-preamble>
function upper_sum_rec(s: string): int

  ensures upper_sum_rec(s) >= 0

{

  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining

}
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)

    ensures res == upper_sum_rec(s)
// </vc-spec>
// <vc-code>
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res + upper_sum_rec(s[i..]) == upper_sum_rec(s)
  {
    res := res + to_int(s[i]);
    i := i + 1;
  }
}
// </vc-code>
