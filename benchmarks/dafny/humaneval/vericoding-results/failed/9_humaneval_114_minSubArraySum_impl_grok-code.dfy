// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): included min function for computing minimum */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed for loop syntax, corrected sum range to q+1, and initialized s properly */
  if |a| == 0 {
    s := 0;
  } else {
    s := Sum(a, 0, 1);
    for p := 0 to |a|-1 {
      for q := p to |a|-1 {
        s := min(s, Sum(a, p, q+1));
      }
    }
  }
}
// </vc-code>
