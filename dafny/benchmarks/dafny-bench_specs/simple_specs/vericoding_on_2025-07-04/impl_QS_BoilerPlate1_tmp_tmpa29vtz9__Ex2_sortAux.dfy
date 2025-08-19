//ATOM


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  ret := [];
  assume ret[..] == a[l..r];
  return ret;
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


//IMPL 

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
 decreases r - l
{
  /* code modified by LLM (iteration 1): fixed base case condition and added proper verification */
  if r - l <= 1 {
    // Base case: empty or single element is already sorted
    assert sorted(a[l..r]);
    return;
  }
  
  var m := l + (r - l) / 2;
  
  /* code modified by LLM (iteration 1): added precondition verification for recursive calls */
  assert 0 <= l < m < r <= a.Length;
  
  sortAux(a, l, m);
  /* code modified by LLM (iteration 1): capture sorted property after first recursive call */
  assert sorted(a[l..m]);
  
  sortAux(a, m, r);
  /* code modified by LLM (iteration 1): capture sorted property after second recursive call */
  assert sorted(a[m..r]);
  
  /* code modified by LLM (iteration 1): verify preconditions for mergeArr call */
  assert 0 <= l < m < r <= a.Length;
  assert sorted(a[l..m]) && sorted(a[m..r]);
  
  mergeArr(a, l, m, r);
}