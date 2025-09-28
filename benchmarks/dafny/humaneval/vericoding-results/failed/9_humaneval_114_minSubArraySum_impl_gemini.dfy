// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int { if x < y then x else y }

function MinSumEndingAt(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  decreases i
{
  if i == 0 then 0
  else min(0, MinSumEndingAt(a, i-1) + a[i-1])
}

/* helper modified by LLM (iteration 5): [added assertions to guide proof of existence postcondition] */
lemma MinSumEndingAt_properties(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures forall k :: 0 <= k <= i ==> Sum(a, k, i) >= MinSumEndingAt(a, i)
  ensures exists k :: 0 <= k <= i && Sum(a, k, i) == MinSumEndingAt(a, i)
  decreases i
{
  if i > 0 {
    MinSumEndingAt_properties(a, i - 1);
    if MinSumEndingAt(a, i - 1) + a[i - 1] < 0 {
      var k_prev :| 0 <= k_prev <= i - 1 && Sum(a, k_prev, i - 1) == MinSumEndingAt(a, i - 1);
      assert Sum(a, k_prev, i) == Sum(a, k_prev, i - 1) + a[i - 1];
    } else {
      assert Sum(a, i, i) == 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [added assertion to establish loop invariant on entry] */
  s := 0;
  var current_min := 0;
  var i := 0;

  assert Sum(a, 0, 0) == 0; // for 'exists' and 'forall' invariants on entry

  while i < |a|
    invariant 0 <= i <= |a|
    invariant current_min == MinSumEndingAt(a, i)
    invariant forall p,q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= s
    invariant exists k, m :: 0 <= k <= m <= i && s == Sum(a, k, m)
  {
    MinSumEndingAt_properties(a, i + 1);
    var next_current_min := min(0, current_min + a[i]);
    s := min(s, next_current_min);
    current_min := next_current_min;
    i := i + 1;
  }
}
// </vc-code>
