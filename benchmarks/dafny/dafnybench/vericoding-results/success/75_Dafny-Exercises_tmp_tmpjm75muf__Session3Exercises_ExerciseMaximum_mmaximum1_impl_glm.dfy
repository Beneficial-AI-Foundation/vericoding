//Algorithm 1: From left to right return the first

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// <vc-code>
{
  i := 0;
  for j := 1 to v.Length 
    invariant 0 <= i < j 
    invariant forall k: int :: 0 <= k < j ==> v[k] <= v[i]
  {
    if v[j] > v[i] {
      i := j;
    }
  }
  return i;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left