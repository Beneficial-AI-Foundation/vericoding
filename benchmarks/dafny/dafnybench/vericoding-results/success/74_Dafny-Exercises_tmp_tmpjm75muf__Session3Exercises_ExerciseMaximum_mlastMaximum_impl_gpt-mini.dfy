//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>

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
  var n := v.Length;
  var imax := 0;
  var j := 1;
  while j < n
    invariant 0 <= imax < n
    invariant 0 <= j <= n
    invariant forall k :: 0 <= k < j ==> v[imax] >= v[k]
    invariant forall l :: imax < l < j ==> v[imax] > v[l]
    decreases n - j
  {
    if v[j] >= v[imax] {
      imax := j;
    }
    j := j + 1;
  }
  i := imax;
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left