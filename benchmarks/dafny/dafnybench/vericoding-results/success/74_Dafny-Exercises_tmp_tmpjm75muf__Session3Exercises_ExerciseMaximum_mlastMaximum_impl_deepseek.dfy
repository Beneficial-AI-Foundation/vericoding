//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
lemma lemma_MaxIndexExists(v: array<int>, lo: int, hi: int) returns (maxIndex: int)
  requires 0 <= lo <= hi < v.Length
  ensures lo <= maxIndex <= hi
  ensures forall k :: lo <= k <= hi ==> v[maxIndex] >= v[k]
{
  maxIndex := lo;
  var current := lo + 1;
  while current <= hi
    invariant lo <= maxIndex <= hi
    invariant current <= hi + 1
    invariant forall k :: lo <= k < current ==> v[maxIndex] >= v[k]
  {
    if v[current] > v[maxIndex] {
      maxIndex := current;
    }
    current := current + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
// </vc-spec>
// <vc-code>
{
  i := v.Length - 1;
  var j := v.Length - 2;
  while j >= 0
    invariant -1 <= j < v.Length
    invariant j < i < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    invariant forall l :: i < l < v.Length ==> v[i] > v[l]
  {
    if v[j] > v[i] {
      i := j;
    } else if v[j] == v[i] {
      // Don't update i when equal to maintain the "last" maximum property
    }
    j := j - 1;
  }
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left