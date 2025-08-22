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
  
  while i < m && j < r
    invariant l <= i <= m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    invariant sorted(temp[..k])
    /* code modified by LLM (iteration 1): fixed variable scope and added proper ordering invariants */
    invariant forall x :: 0 <= x < k && i < m ==> temp[x] <= a[i]
    invariant forall x :: 0 <= x < k && j < r ==> temp[x] <= a[j]
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: l <= y < i && temp[x] == a[y]) || 
      (exists y :: m <= y < j && temp[x] == a[y])
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
    invariant sorted(temp[..k])
    /* code modified by LLM (iteration 1): fixed variable scope in invariant */
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: l <= y < i && temp[x] == a[y]) || 
      (exists y :: m <= y < r && temp[x] == a[y])
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < r
    invariant i == m && m <= j <= r && 0 <= k <= r - l
    invariant k == (i - l) + (j - m)
    invariant sorted(temp[..k])
    /* code modified by LLM (iteration 1): fixed variable scope in invariant */
    invariant forall x :: 0 <= x < k ==> 
      (exists y :: l <= y < m && temp[x] == a[y]) || 
      (exists y :: m <= y < j && temp[x] == a[y])
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  k := 0;
  while k < r - l
    invariant 0 <= k <= r - l
    invariant a[l..l+k] == temp[..k]
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    /* code modified by LLM (iteration 1): simplified invariant to avoid array modification conflicts */
    invariant forall x :: r <= x < a.Length ==> a[x] == old(a[x])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
}

//IMPL Ex3
method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  decreases r - l
{
  if r - l > 1 {
    var m := l + (r - l) / 2;
    /* code modified by LLM (iteration 1): added assertion to ensure valid middle point */
    assert l < m < r;
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
  }
}