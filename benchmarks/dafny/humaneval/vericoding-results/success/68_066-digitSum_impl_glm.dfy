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
/* code modified by LLM (iteration 2): changed to use string slicing to match recursive definition */
{
  var t := s;
  var sum := 0;
  while |t| > 0
    invariant sum + upper_sum_rec(t) == upper_sum_rec(s)
  {
    sum := sum + to_int(t[0]);
    t := t[1..];
  }
  res := sum;
}
// </vc-code>
