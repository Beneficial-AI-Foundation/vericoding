function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumEmpty(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures Sum(a, i, i) == 0
{
}

lemma SumExtend(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
}

lemma SumSingleton(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a, i, i+1) == a[i]
{
  SumExtend(a, i, i);
  SumEmpty(a, i);
}

lemma SumShift(a: seq<int>, s: int, t: int)
  requires 0 <= s < t <= |a|
  ensures Sum(a, s, t) == Sum(a, s+1, t) + a[s]
{
  if t == s + 1 {
    SumSingleton(a, s);
    SumEmpty(a, t);
  } else {
    SumShift(a, s+1, t);
  }
}
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)
  // post-conditions-start
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  s := 0;
  if |a| == 0 {
    return;
  }
  
  var minEndingHere := a[0];
  var minSoFar := a[0];
  var i := 1;
  
  SumSingleton(a, 0);
  
  while i < |a|
    invariant 1 <= i <= |a|
    invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= minSoFar
    invariant exists k, m :: 0 <= k <= m <= i && minSoFar == Sum(a, k, m)
    invariant forall q :: 0 <= q <= i ==> Sum(a, q, i) >= minEndingHere
    invariant exists k :: 0 <= k <= i && minEndingHere == Sum(a, k, i)
  {
    var prevMinEndingHere := minEndingHere;
    var k :| 0 <= k <= i && prevMinEndingHere == Sum(a, k, i);
    
    SumExtend(a, k, i);
    assert Sum(a, k, i+1) == prevMinEndingHere + a[i];
    
    SumSingleton(a, i);
    
    if prevMinEndingHere > 0 {
      minEndingHere := a[i];
      assert minEndingHere == Sum(a, i, i+1);
    } else {
      minEndingHere := prevMinEndingHere + a[i];
      assert minEndingHere == Sum(a, k, i+1);
    }
    
    if minEndingHere < minSoFar {
      minSoFar := minEndingHere;
    }
    
    i := i + 1;
  }
  
  s := minSoFar;
}
// </vc-code>

