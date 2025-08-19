//ATOM
//Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
  i := 0;
  assume {:axiom} 0<=i<v.Length;
  assume {:axiom} forall k:: 0<=k<v.Length ==> v[i]>=v[k];
  return i;
}

//IMPL mmaxvalue1

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
  /* code modified by LLM (iteration 1): Implemented linear scan algorithm from left to right to find maximum value */
  m := v[0];
  var i := 1;
  
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant m in v[..]
    invariant forall k :: 0 <= k < i ==> m >= v[k]
  {
    if v[i] > m {
      m := v[i];
    }
    i := i + 1;
  }
}