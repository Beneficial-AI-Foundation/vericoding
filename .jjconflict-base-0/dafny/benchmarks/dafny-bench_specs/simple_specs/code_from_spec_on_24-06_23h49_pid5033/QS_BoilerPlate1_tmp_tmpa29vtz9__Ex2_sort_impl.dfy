//ATOM

// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  ret := new int[r - l];
  assume ret[..] == a[l..r];
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
  assume a[..l] == old(a[..l]);
  assume a[r..] == old(a[r..]);
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
  assume a[..l] == old(a[..l]);
  assume a[r..] == old(a[r..]);
}

//IMPL Ex3

method sort(a : array<int>) 
 ensures sorted(a[..])
 modifies a
{
  /* code modified by LLM (iteration 1): Added check for array length > 1 since sortAux requires l < r */
  if a.Length > 1 {
    sortAux(a, 0, a.Length);
  }
  /* code modified by LLM (iteration 1): Added else case to handle empty arrays and single-element arrays which are trivially sorted */
  else {
    // Arrays with 0 or 1 elements are already sorted
    assert sorted(a[..]);
  }
}