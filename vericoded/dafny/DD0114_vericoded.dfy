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
  var j := 1;
  
  while j < v.Length
    invariant 0 <= i < j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left