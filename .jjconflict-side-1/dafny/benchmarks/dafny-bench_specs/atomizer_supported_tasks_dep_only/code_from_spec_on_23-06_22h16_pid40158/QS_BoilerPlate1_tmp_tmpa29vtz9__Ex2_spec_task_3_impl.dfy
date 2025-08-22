// ATOM 
function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

//IMPL Ex1
method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{
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

//IMPL Ex2
method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a 
{
  var temp := new int[r - l];
  var i := l;
  var j := m;
  var k := 0;
  
  /* code modified by LLM (iteration 1): ghost variables to track original array state */
  ghost var originalA := a[..];
  
  while i < m && j < r
    invariant l <= i <= m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    /* code modified by LLM (iteration 1): comprehensive invariants for merge correctness */
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(originalA[l..i]) + multiset(originalA[m..j])
    invariant forall x :: 0 <= x < k && i < m ==> temp[x] <= a[i]
    invariant forall x :: 0 <= x < k && j < r ==> temp[x] <= a[j]
    invariant a[..] == originalA
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
  
  while i < m
    invariant l <= i <= m && j == r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    /* code modified by LLM (iteration 1): invariants for copying remaining left elements */
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(originalA[l..i]) + multiset(originalA[m..r])
    invariant forall x :: 0 <= x < k && i < m ==> temp[x] <= a[i]
    invariant a[..] == originalA
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < r
    invariant i == m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    /* code modified by LLM (iteration 1): invariants for copying remaining right elements */
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(originalA[l..m]) + multiset(originalA[m..j])
    invariant forall x :: 0 <= x < k && j < r ==> temp[x] <= a[j]
    invariant a[..] == originalA
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): copy temp back to original array */
  k := 0;
  while k < r - l
    invariant 0 <= k <= r - l
    invariant a[l..l+k] == temp[..k]
    invariant a[..l] == originalA[..l]
    invariant a[r..] == originalA[r..]
    invariant forall x :: l + k <= x < r ==> a[x] == originalA[x]
    invariant sorted(temp[..])
    invariant multiset(temp[..]) == multiset(originalA[l..r])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
}

//IMPL Ex3
method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
{
  if a.Length > 1 {
    sortAux(a, 0, a.Length);
  }
}

//IMPL sortAux
method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  /* code modified by LLM (iteration 1): termination measure */
  decreases r - l
{
  if r - l > 1 {
    var m := l + (r - l) / 2;
    /* code modified by LLM (iteration 1): assertions to help verification */
    assert l < m < r;
    
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
  }
}