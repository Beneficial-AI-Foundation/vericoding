method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  /* code modified by LLM (iteration 1): implemented array copying with proper allocation */
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

//IMPL sortAux
method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
 /* code modified by LLM (iteration 3): added decreases clause for termination */
 decreases r - l
{
  /* code modified by LLM (iteration 1): implemented merge sort algorithm */
  if r - l <= 1 {
    return;
  }
  
  var m := (l + r) / 2;
  sortAux(a, l, m);
  sortAux(a, m, r);
  mergeArr(a, l, m, r);
}

//IMPL sorted
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

//IMPL mergeArr
method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  /* code modified by LLM (iteration 1): implemented merging of two sorted subarrays */
  var leftArr := copyArr(a, l, m);
  var rightArr := copyArr(a, m, r);
  
  var i, j, k := 0, 0, l;
  
  while i < leftArr.Length && j < rightArr.Length
    invariant 0 <= i <= leftArr.Length
    invariant 0 <= j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant sorted(a[l..k])
    invariant forall x :: l <= x < k && i < leftArr.Length ==> a[x] <= leftArr[i]
    invariant forall x :: l <= x < k && j < rightArr.Length ==> a[x] <= rightArr[j]
  {
    if leftArr[i] <= rightArr[j] {
      a[k] := leftArr[i];
      i := i + 1;
    } else {
      a[k] := rightArr[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): strengthened invariants to maintain sorted property */
  while i < leftArr.Length
    invariant 0 <= i <= leftArr.Length
    invariant j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant sorted(a[l..k])
    invariant j == rightArr.Length
    invariant k > l ==> (forall x :: i <= x < leftArr.Length ==> a[k-1] <= leftArr[x])
  {
    a[k] := leftArr[i];
    i := i + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): strengthened invariants to maintain sorted property */
  while j < rightArr.Length
    invariant i <= leftArr.Length
    invariant 0 <= j <= rightArr.Length
    invariant l <= k <= r
    invariant k == l + i + j
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant leftArr[..] == old(a[l..m])
    invariant rightArr[..] == old(a[m..r])
    invariant sorted(a[l..k])
    invariant i == leftArr.Length
    invariant k > l ==> (forall x :: j <= x < rightArr.Length ==> a[k-1] <= rightArr[x])
  {
    a[k] := rightArr[j];
    j := j + 1;
    k := k + 1;
  }
}

//IMPL sort
method sort(a : array<int>) 
 ensures sorted(a[..])
 modifies a
{
  /* code modified by LLM (iteration 1): added check for non-empty array before calling sortAux */
  if a.Length > 0 {
    sortAux(a, 0, a.Length);
  }
}