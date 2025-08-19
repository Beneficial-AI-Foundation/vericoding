method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  /* code modified by LLM (iteration 1): Fixed array creation and sequence equality */
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
  /* code modified by LLM (iteration 4): Fixed merge implementation with corrected invariants and bounds */
  var temp := new int[r - l];
  var i, j, k := l, m, 0;
  
  // Merge phase
  while i < m && j < r
    invariant l <= i <= m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant k > 0 && i < m ==> temp[k-1] <= a[i]
    invariant k > 0 && j < r ==> temp[k-1] <= a[j]
    invariant forall x :: 0 <= x < k ==> temp[x] in multiset(a[l..i]) + multiset(a[m..j])
  {
    if a[i] <= a[j] {
      temp[k] := a[i];
      i := i + 1;
    } else {
      temp[k] := a[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  // Copy remaining elements from left subarray
  while i < m
    invariant l <= i <= m && j == r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant k > 0 && i < m ==> temp[k-1] <= a[i]
    invariant forall x :: 0 <= x < k ==> temp[x] in multiset(a[l..i]) + multiset(a[m..j])
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  // Copy remaining elements from right subarray
  while j < r
    invariant i == m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant k > 0 && j < r ==> temp[k-1] <= a[j]
    invariant forall x :: 0 <= x < k ==> temp[x] in multiset(a[l..i]) + multiset(a[m..j])
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  // Copy back to original array
  k := 0;
  /* code modified by LLM (iteration 4): Added ghost variable to preserve old array state */
  ghost var oldA := a[..];
  while k < r - l
    invariant 0 <= k <= r - l
    invariant a[..l] == oldA[..l]
    invariant a[r..] == oldA[r..]
    invariant a[l..l+k] == temp[..k]
    invariant sorted(temp[..])
    invariant multiset(temp[..]) == multiset(oldA[l..r])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
}


//IMPL 

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
 /* code modified by LLM (iteration 2): Added decreases clause for termination */
 decreases r - l
{
  if r - l == 1 {
    // Base case: single element is already sorted
    return;
  }
  
  var m := l + (r - l) / 2;
  sortAux(a, l, m);
  sortAux(a, m, r);
  mergeArr(a, l, m, r);
}