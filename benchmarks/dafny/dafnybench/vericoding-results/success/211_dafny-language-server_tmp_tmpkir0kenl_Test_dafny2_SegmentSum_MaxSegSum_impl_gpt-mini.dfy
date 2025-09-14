// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var curS := 0;
  k := 0;
  m := 0;
  var bestSum := 0;

  while curS <= n
    invariant 0 <= curS <= n + 1
    invariant 0 <= k <= m <= n
    invariant bestSum == Sum(a, k, m)
    invariant forall p,q :: 0 <= p <= q <= n && p < curS ==> Sum(a, p, q) <= bestSum
    decreases n - curS + 1
  {
    var curE := curS;
    while curE <= n
      invariant 0 <= curS <= n + 1
      invariant curS <= curE <= n + 1
      invariant 0 <= k <= m <= n
      invariant bestSum == Sum(a, k, m)
      invariant forall p,q :: 0 <= p <= q <= n && (p < curS || (p == curS && q < curE)) ==> Sum(a, p, q) <= bestSum
      decreases n - curE + 1
    {
      var candidate := Sum(a, curS, curE);
      if candidate > bestSum {
        bestSum, k, m := candidate, curS, curE;
      }
      curE := curE + 1;
    }
    curS := curS + 1;
  }
}
// </vc-code>

