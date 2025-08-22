//ATOM


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  ret := [];
  assume ret[..] ==> a[l..r];
  return ret;
}


//ATOM

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//ATOM


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


// SPEC

// Ex3

method sort(a : array<int>) 
 ensures sorted(a[..])
 modifies a
{
}
