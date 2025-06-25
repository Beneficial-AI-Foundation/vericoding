//ATOM

// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  /* code modified by LLM (iteration 1): Fixed compilation error - create array with proper size instead of empty sequence */
  ret := new int[r - l];
  var i := 0;
  while i < r - l
    invariant 0 <= i <= r - l
    invariant ret[..i] == a[l..l+i]
  {
    ret[i] := a[l + i];
    i := i + 1;
  }
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

//IMPL sortAux

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
{
  if r - l == 1 {
    /* code modified by LLM (iteration 1): Added assertion to help verify base case postcondition */
    assert a[l..r] == [a[l]];
    assert sorted(a[l..r]);
    return;
  }
  
  var m := l + (r - l) / 2;
  
  /* code modified by LLM (iteration 1): Added assertion to help verify valid range for recursive calls */
  assert l < m < r;
  
  sortAux(a, l, m);
  
  sortAux(a, m, r);
  /* code modified by LLM (iteration 1): Use postconditions from recursive calls to establish preconditions for mergeArr */
  assert sorted(a[l..m]);
  assert sorted(a[m..r]);
  
  mergeArr(a, l, m, r);
}