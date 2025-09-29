predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }

// <vc-helpers>
lemma IsPeekFromGe(v: array<int>, i: int, idx: int)
  requires 0 <= idx < i < v.Length
  requires forall k :: 0 <= k < i ==> v[idx] >= v[k]
  ensures v[i] >= v[idx] ==> (forall k :: 0 <= k < i ==> v[i] >= v[k])
{
  if v[i] >= v[idx] {
    forall k | 0 <= k < i {
      calc {
        v[i];
        >= v[idx];
        >= v[k];
      }
    }
  }
}

lemma NotIsPeekFromLt(v: array<int>, i: int, idx: int)
  requires 0 <= idx < i < v.Length
  requires forall k :: 0 <= k < i ==> v[idx] >= v[k]
  ensures v[i] < v[idx] ==> !(forall k :: 0 <= k < i ==> v[i] >= v[k])
{
  if v[i] < v[idx] {
    // witness k = idx to refute the universal property
    assert 0 <= idx < i;
    assert v[i] < v[idx];
    assert !(forall k0 :: 0 <= k0 < i ==> v[i] >= v[k0]);
  }
}
// </vc-helpers>

// <vc-spec>
method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
  var i := 1;
  sum := v[0];
  var maxIdx := 0;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant 0 <= maxIdx < i
    invariant forall k :: 0 <= k < i ==> v[maxIdx] >= v[k]
    invariant sum == peekSum(v, i)
  {
    if v[i] >= v[maxIdx] {
      IsPeekFromGe(v, i, maxIdx);
      assert forall k :: 0 <= k < i ==> v[i] >= v[k];
      sum := sum + v[i];
      maxIdx := i;
    } else {
      NotIsPeekFromLt(v, i, maxIdx);
      assert !(forall k :: 0 <= k < i ==> v[i] >= v[k]);
      // sum unchanged
    }
    i := i + 1;
  }
}
// </vc-code>

