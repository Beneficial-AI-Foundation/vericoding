method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
// </vc-spec>
// <vc-code>
{
  i := 0;
  var j := 1;
  
  while j < v.Length
    invariant 0 <= i < v.Length
    invariant 1 <= j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left