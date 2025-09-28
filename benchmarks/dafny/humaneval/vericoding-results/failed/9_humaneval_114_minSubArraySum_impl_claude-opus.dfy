// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas for sum properties and minimum tracking */
lemma EmptySum(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures Sum(a, i, i) == 0
{
  // By definition of Sum
}

lemma SumExtend(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
  // Proof by definition of Sum
}

lemma SumSingle(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a, i, i+1) == a[i]
{
  assert Sum(a, i, i+1) == Sum(a, i, i) + a[i];
  assert Sum(a, i, i) == 0;
}

lemma SubarraySum(a: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |a|
  ensures Sum(a, i, k) == Sum(a, i, j) + Sum(a, j, k)
{
  if j == k {
    assert Sum(a, j, k) == 0;
  } else if i == j {
    assert Sum(a, i, j) == 0;
  } else {
    SubarraySum(a, i, j, k-1);
    assert Sum(a, i, k) == Sum(a, i, k-1) + a[k-1];
    assert Sum(a, j, k) == Sum(a, j, k-1) + a[k-1];
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
  /* code modified by LLM (iteration 5): Strengthened invariants to prove all subarrays are >= s */
  if |a| == 0 {
    s := 0;
    assert Sum(a, 0, 0) == 0 by { EmptySum(a, 0); }
    return;
  }
  
  s := a[0];
  assert Sum(a, 0, 1) == a[0] by { SumSingle(a, 0); }
  
  var minEndingHere := a[0];
  var minStart := 0;
  var bestStart := 0;
  var bestEnd := 1;
  var i := 1;
  
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= minStart < i
    invariant 0 <= bestStart < bestEnd <= i
    invariant minEndingHere == Sum(a, minStart, i)
    invariant s == Sum(a, bestStart, bestEnd)
    invariant s <= minEndingHere
    invariant forall j :: 0 <= j < i ==> s <= a[j]
    invariant forall p, q :: 0 <= p < q <= i ==> Sum(a, p, q) >= s
    invariant forall k :: 0 <= k < i ==> Sum(a, k, i) >= minEndingHere
  {
    assert Sum(a, i, i+1) == a[i] by { SumSingle(a, i); }
    
    if minEndingHere > 0 {
      minEndingHere := a[i];
      minStart := i;
      assert minEndingHere == Sum(a, minStart, i+1) by { SumSingle(a, i); }
    } else {
      var oldMinEndingHere := minEndingHere;
      minEndingHere := minEndingHere + a[i];
      assert oldMinEndingHere == Sum(a, minStart, i);
      assert minEndingHere == Sum(a, minStart, i+1) by {
        SubarraySum(a, minStart, i, i+1);
        SumSingle(a, i);
      }
    }
    
    if minEndingHere < s {
      s := minEndingHere;
      bestStart := minStart;
      bestEnd := i + 1;
    }
    
    i := i + 1;
  }
  
  assert i == |a|;
  assert forall p, q :: 0 <= p < q <= |a| ==> Sum(a, p, q) >= s;
  assert bestStart < bestEnd <= |a|;
  assert s == Sum(a, bestStart, bestEnd);
}
// </vc-code>
