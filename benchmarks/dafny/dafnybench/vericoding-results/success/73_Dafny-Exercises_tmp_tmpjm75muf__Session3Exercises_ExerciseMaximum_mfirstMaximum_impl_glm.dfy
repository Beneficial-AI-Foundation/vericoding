//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
// No changes to helpers needed; fix is in loop invariants.
// </vc-helpers>

// <vc-spec>
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
// </vc-spec>
// <vc-code>
{
  var maxIndex := 0;
  var maxValue := v[0];
  var j := 1;
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant 0 <= maxIndex < j
    invariant maxValue == v[maxIndex]
    invariant forall k :: 0 <= k < j ==> maxValue >= v[k]
    invariant forall l :: 0 <= l < maxIndex ==> v[maxIndex] > v[l]
  {
    if v[j] > maxValue {
      maxIndex := j;
      maxValue := v[j];
    }
    j := j + 1;
  }
  return maxIndex;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left