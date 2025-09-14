//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>
// No helper lemmas required for this proof.
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
  var imax := 0;
  var k := 1;
  while k < v.Length
    invariant 0 <= imax < v.Length
    invariant 0 <= k <= v.Length
    invariant forall j :: 0 <= j < k ==> v[imax] >= v[j]
    invariant forall l :: 0 <= l < imax ==> v[imax] > v[l]
    decreases v.Length - k
  {
    if v[k] > v[imax] {
      imax := k;
    }
    k := k + 1;
  }
  i := imax;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left