//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]

{
  assume false;
}

//Algorithm : from left to right
//Algorithm : from right to left