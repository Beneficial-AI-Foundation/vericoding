//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  i := v.Length - 1;
  var j := v.Length - 2;
  
  while j >= 0
    invariant -1 <= j < v.Length - 1
    invariant j < i < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    invariant forall l :: i < l < v.Length ==> v[i] > v[l]
    decreases j + 1
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j - 1;
  }
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left