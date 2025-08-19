method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  /* code modified by LLM (iteration 1): Fixed compilation error by removing assume statements and implementing proper array copy */
  ret := new int[r - l];
  var i := 0;
  while i < r - l
    invariant 0 <= i <= r - l
    invariant ret[..i] == a[l..l+i]
  {
    ret[i] := a[l + i];
    i := i + 1;
  }
}


//IMPL

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
/* code modified by LLM (iteration 3): Added decreases clause to fix termination */
 decreases r - l
{
  /* code modified by LLM (iteration 2): Implemented merge sort with proper base case and recursive calls */
  if r - l <= 1 {
    // Base case: already sorted
    return;
  }
  
  var mid := l + (r - l) / 2;
  sortAux(a, l, mid);
  sortAux(a, mid, r);
  mergeArr(a, l, mid, r);
}


//IMPL
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//IMPL

// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  /* code modified by LLM (iteration 4): Complete rewrite of merge implementation with correct invariants */
  ghost var old_a := a[..];
  var temp := new int[r - l];
  var i, j, k := l, m, 0;
  
  // Merge the two sorted subarrays
  while i < m && j < r
    invariant l <= i <= m && m <= j <= r && k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: (l <= y < i && temp[x] == old_a[y]) || (m <= y < j && temp[x] == old_a[y]))
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
    invariant l <= i <= m && j == r && k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: (l <= y < i && temp[x] == old_a[y]) || (m <= y < j && temp[x] == old_a[y]))
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  // Copy remaining elements from right subarray
  while j < r
    invariant i == m && m <= j <= r && k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: (l <= y < i && temp[x] == old_a[y]) || (m <= y < j && temp[x] == old_a[y]))
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  // Copy back to original array
  k := 0;
  /* code modified by LLM (iteration 4): Simplified invariants for copying back */
  while k < r - l
    invariant 0 <= k <= r - l
    invariant a[..l] == old_a[..l]
    invariant a[r..] == old_a[r..]
    invariant forall x :: 0 <= x < k ==> a[l + x] == temp[x]
    invariant forall x, y {:trigger temp[x], temp[y]} :: 0 <= x < y < k ==> a[l + x] <= a[l + y]
    invariant k > 0 ==> (forall x {:trigger a[l + x], a[l + x + 1]} :: 0 <= x < k - 1 ==> a[l + x] <= a[l + x + 1])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Added assertion to establish final sortedness */
  assert k == r - l;
  assert forall x :: 0 <= x < r - l ==> a[l + x] == temp[x];
  assert forall x, y :: 0 <= x < y < r - l ==> temp[x] <= temp[y];
}


//IMPL Ex3

method sort(a : array<int>) 
 ensures sorted(a[..])
 modifies a
{
  /* code modified by LLM (iteration 1): Fixed compilation error by removing explanatory text and implementing proper edge case handling */
  if a.Length > 0 {
    sortAux(a, 0, a.Length);
  }
}