// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumSplit(a: seq<int>, s: int, mid: int, t: int)
  requires 0 <= s <= mid <= t <= |a|
  ensures Sum(a, s, t) == Sum(a, s, mid) + Sum(a, mid, t)
{
  if s == mid {
    assert Sum(a, s, mid) == 0;
    assert Sum(a, s, t) == Sum(a, mid, t);
  } else if mid == t {
    assert Sum(a, mid, t) == 0;
    assert Sum(a, s, t) == Sum(a, s, mid);
  } else {
    calc {
      Sum(a, s, t);
      Sum(a, s, t-1) + a[t-1];
      { SumSplit(a, s, mid, t-1); }
      Sum(a, s, mid) + Sum(a, mid, t-1) + a[t-1];
      Sum(a, s, mid) + Sum(a, mid, t);
    }
  }
}

lemma SumExtendRight(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
  calc {
    Sum(a, s, t+1);
    Sum(a, s, t) + a[t];
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>
// </vc-spec>

// <vc-code>
method MaxSegSumImpl(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  if |a| == 0 {
    return 0, 0;
  }
  
  var best_sum := a[0];
  var best_start := 0;
  var best_end := 1;
  var current_sum := a[0];
  var current_start := 0;
  var i := 1;

  while i <= |a|
    decreases |a| - i
    invariant 0 <= best_start <= best_end <= i <= |a| + 1
    invariant 0 <= current_start <= i <= |a| + 1
    invariant i <= |a| ==> current_sum == Sum(a, current_start, i)
    invariant best_sum == Sum(a, best_start, best_end)
    invariant forall p, q :: 0 <= p <= q <= i && q <= |a| ==> Sum(a, p, q) <= best_sum
  {
    if i < |a| {
      if current_sum <= 0 {
        current_sum := a[i];
        current_start := i;
      } else {
        current_sum := current_sum + a[i];
        SumExtendRight(a, current_start, i);
      }
      i := i + 1;
      if current_sum > best_sum {
        best_sum := current_sum;
        best_start := current_start;
        best_end := i;
      }
    } else {
      break;
    }
  }
  
  if best_sum < 0 {
    var max_val := a[0];
    var max_idx := 0;
    i := 1;
    while i < |a|
      decreases |a| - i
      invariant 0 <= max_idx < i <= |a|
      invariant max_val == a[max_idx]
      invariant forall j :: 0 <= j < i ==> a[j] <= max_val
    {
      if a[i] > max_val {
        max_val := a[i];
        max_idx := i;
      }
      i := i + 1;
    }
    best_sum := max_val;
    best_start := max_idx;
    best_end := max_idx + 1;
  }
  
  k := best_start;
  m := best_end;
  return k, m;
}
// </vc-code>
