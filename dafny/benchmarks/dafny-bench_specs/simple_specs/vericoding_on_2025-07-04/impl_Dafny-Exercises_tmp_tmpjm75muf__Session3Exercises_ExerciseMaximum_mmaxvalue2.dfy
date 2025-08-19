//ATOM

//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
  i := 0;
  assume 0<=i<v.Length;
  assume forall k:: 0<=k<v.Length ==> v[i]>=v[k];
  return i;
}

//IMPL 

method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
  var i := mmaximum2(v);
  m := v[i];
}