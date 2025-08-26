//Algorithm 1: From left to right return the first

// <vc-helpers>
// </vc-helpers>

method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// <vc-code>
{
  assume false;
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left