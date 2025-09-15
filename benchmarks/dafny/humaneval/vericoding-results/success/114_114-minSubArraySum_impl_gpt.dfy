// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): basic min utility */
function intMin(a: int, b: int): int { if a <= b then a else b }
/* helper modified by LLM (iteration 2): bounds check predicate */
predicate InBounds(i: int, n: int) { 0 <= i <= n }
/* helper modified by LLM (iteration 2): range validity predicate */
predicate RangeOK(p: int, q: int, n: int) { 0 <= p <= q <= n }
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): exhaustive search with strengthened loop invariants and proper bounds */
  var n := |a|;
  var k := 0;
  var m := 0;
  s := Sum(a, 0, 0);
  var p := 0;
  while p <= n
    invariant 0 <= p <= n + 1
    invariant 0 <= k <= m <= n
    invariant s == Sum(a, k, m)
    invariant forall p0, q0 :: 0 <= p0 < p && p0 <= q0 <= n ==> Sum(a, p0, q0) >= s
    decreases n - p + 1
  {
    var q := p;
    while q <= n
      invariant p <= q <= n + 1
      invariant 0 <= k <= m <= n
      invariant s == Sum(a, k, m)
      invariant forall q0 :: p <= q0 < q ==> Sum(a, p, q0) >= s
      invariant forall p0, q0 :: 0 <= p0 < p && p0 <= q0 <= n ==> Sum(a, p0, q0) >= s
      decreases n - q + 1
    {
      var w := Sum(a, p, q);
      if w < s {
        s := w;
        k := p;
        m := q;
      }
      q := q + 1;
    }
    p := p + 1;
  }
}
// </vc-code>
