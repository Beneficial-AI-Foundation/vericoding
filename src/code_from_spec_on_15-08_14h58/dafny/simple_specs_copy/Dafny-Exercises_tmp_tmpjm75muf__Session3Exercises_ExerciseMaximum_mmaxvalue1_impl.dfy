//ATOM
//Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
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
method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
  /* code modified by LLM (iteration 1): call mmaximum1 to get index of maximum element */
  var i := mmaximum1(v);
  /* code modified by LLM (iteration 1): set m to the value at the maximum index */
  m := v[i];
}