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
function upper_sum_rec_helper(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures upper_sum_rec_helper(s, i) == upper_sum_rec(s[i..])
  decreases |s| - i
{
  if i == |s| then
    0
  else
    to_int(s[i]) + upper_sum_rec_helper(s, i+1)
}
// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)

    ensures res == upper_sum_rec(s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added proper termination */
  res := upper_sum_rec_helper(s, 0);
}
// </vc-code>
