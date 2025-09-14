//Algorithm 1: From left to right return the first

// <vc-helpers>
// no helpers required
// </vc-helpers>

// <vc-spec>
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// <vc-code>
{
  var imax := 0;
  var j := 1;
  while j < v.Length
    invariant 0 <= imax < v.Length
    invariant 0 <= j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[imax] >= v[k]
  {
    if v[j] > v[imax] {
      imax := j;
    }
    j := j + 1;
  }
  i := imax;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left