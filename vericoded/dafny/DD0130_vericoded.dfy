function min(v:array<int>,i:int):int
decreases i
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {if (i==1) then v[0]
  else if (v[i-1]<=min(v,i-1)) then v[i-1]
  else min(v,i-1)
  }


function countMin(v:array<int>,x:int, i:int):int
decreases i
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {
   if (i==0) then 0
   else if (v[i-1]==x) then 1+countMin(v,x,i-1)
   else countMin(v,x,i-1)

  }

// <vc-helpers>
lemma UpdateMinCount(v: array<int>, i: int, oldMin: int, oldCount: int)
  requires 1 <= i < v.Length
  requires oldMin == min(v, i)
  requires oldCount == countMin(v, oldMin, i)
  ensures (if v[i] < oldMin then v[i] else oldMin) == min(v, i+1)
  ensures (if v[i] < oldMin then 1 else if v[i] == oldMin then oldCount + 1 else oldCount)
          == countMin(v, (if v[i] < oldMin then v[i] else oldMin), i+1)
  decreases v.Length - i
{
  var a := v[i];
  if a < oldMin {
    // min
    assert min(v, i) == oldMin;
    assert min(v, i+1) == (if a <= oldMin then a else oldMin);
    // a <= oldMin holds because a < oldMin
    assert a <= oldMin;
    assert min(v, i+1) == a;

    // count: a < oldMin implies a is not in v[0..i)
    // from min's postcondition: forall k :: 0 <= k < i ==> v[k] >= min(v,i)
    assert (forall k :: 0 <= k < i ==> v[k] >= min(v, i));
    assert (forall k :: 0 <= k < i ==> v[k] >= oldMin);
    // since a < oldMin, for all k v[k] > a, so none equal a
    assert (forall k :: 0 <= k < i ==> v[k] != a);
    // therefore countMin(v,a,i) == 0
    assert !(a in v[0..i]);
    assert countMin(v, a, i) == 0;

    // now countMin for i+1: v[i] == a, so countMin(v,a,i+1) = 1 + countMin(v,a,i) = 1
    assert countMin(v, a, i+1) == (if a == a then 1 + countMin(v, a, i) else countMin(v, a, i));
    assert countMin(v, a, i+1) == 1 + 0;
  } else if a == oldMin {
    // min
    assert min(v, i) == oldMin;
    assert min(v, i+1) == (if a <= oldMin then a else oldMin);
    // a == oldMin implies a <= oldMin, so min(v,i+1) == a == oldMin
    assert min(v, i+1) == oldMin;

    // count: since v[i] == oldMin, countMin(v,oldMin,i+1) = 1 + countMin(v,oldMin,i)
    assert countMin(v, oldMin, i+1) == (if a == oldMin then 1 + countMin(v, oldMin, i) else countMin(v, oldMin, i));
    assert countMin(v, oldMin, i+1) == 1 + oldCount;
  } else {
    // a > oldMin
    // min stays oldMin
    assert min(v, i) == oldMin;
    assert !(a <= oldMin);
    assert min(v, i+1) == (if a <= oldMin then a else oldMin);
    assert min(v, i+1) == oldMin;

    // count: v[i] != oldMin so count remains oldCount
    assert countMin(v, oldMin, i+1) == (if a == oldMin then 1 + countMin(v, oldMin, i) else countMin(v, oldMin, i));
    assert countMin(v, oldMin, i+1) == oldCount;
  }
}
// </vc-helpers>

// <vc-spec>
method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm
// </vc-spec>
// <vc-code>
{
  var n := v.Length;
  var mn := v[0];
  var cnt := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant mn == min(v, i)
    invariant cnt == countMin(v, mn, i)
    decreases n - i
  {
    var a := v[i];
    var newMin := if a < mn then a else mn;
    var newCount := if a < mn then 1 else if a == mn then cnt + 1 else cnt;
    UpdateMinCount(v, i, mn, cnt);
    mn := newMin;
    cnt := newCount;
    i := i + 1;
  }
  c := cnt;
}
// </vc-code>

