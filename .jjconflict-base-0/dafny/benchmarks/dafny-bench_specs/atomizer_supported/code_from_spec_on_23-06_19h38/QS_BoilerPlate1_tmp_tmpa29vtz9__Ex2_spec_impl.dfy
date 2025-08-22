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
  
  /* code modified by LLM (iteration 1): Main merge loop with comprehensive invariants */
  while i < m && j < r
    invariant l <= i <= m
    invariant m <= j <= r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x :: 0 <= x < k - 1 ==> temp[x] <= temp[x + 1]
    invariant forall x :: l <= x < i ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant forall x :: m <= x < j ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant i < m && j < r ==> (k > 0 ==> temp[k-1] <= a[i] && temp[k-1] <= a[j])
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
  
  /* code modified by LLM (iteration 1): Copy remaining elements from left half */
  while i < m
    invariant l <= i <= m
    invariant j == r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x :: 0 <= x < k - 1 ==> temp[x] <= temp[x + 1]
    invariant forall x :: l <= x < i ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant forall x :: m <= x < r ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant i < m ==> (k > 0 ==> temp[k-1] <= a[i])
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Copy remaining elements from right half */
  while j < r
    invariant i == m
    invariant m <= j <= r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant forall x :: 0 <= x < k - 1 ==> temp[x] <= temp[x + 1]
    invariant forall x :: l <= x < m ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant forall x :: m <= x < j ==> exists y :: 0 <= y < k && temp[y] == a[x]
    invariant j < r ==> (k > 0 ==> temp[k-1] <= a[j])
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Establish that temp is sorted */
  assert k == r - l;
  assert forall x :: 0 <= x < k - 1 ==> temp[x] <= temp[x + 1];
  
  /* code modified by LLM (iteration 1): Helper lemma call */
  lemma_sorted_from_adjacent(temp[..k]);
  
  k := 0;
  /* code modified by LLM (iteration 1): Copy back to original array */
  while k < r - l
    invariant 0 <= k <= r - l
    invariant forall x :: 0 <= x < k ==> a[l + x] == temp[x]
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant forall x :: l + k <= x < r ==> a[x] == old(a[x])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Final assertions */
  assert a[l..r] == temp[..];
  assert sorted(temp[..]);
}

/* code modified by LLM (iteration 1): Helper lemma for sorted property */
lemma lemma_sorted_from_adjacent(s: seq<int>)
  requires forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
  ensures sorted(s)
{
  if |s| <= 1 {
    return;
  }
  
  forall k1, k2 | 0 <= k1 <= k2 < |s| 
    ensures s[k1] <= s[k2]
  {
    if k1 == k2 {
      assert s[k1] <= s[k2];
    } else {
      lemma_transitivity(s, k1, k2);
    }
  }
}

/* code modified by LLM (iteration 1): Helper lemma for transitivity */
lemma lemma_transitivity(s: seq<int>, k1: int, k2: int)
  requires 0 <= k1 < k2 < |s|
  requires forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
  ensures s[k1] <= s[k2]
{
  if k1 + 1 == k2 {
    assert s[k1] <= s[k2];
  } else {
    lemma_transitivity(s, k1, k2 - 1);
    assert s[k1] <= s[k2 - 1] <= s[k2];
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
  /* code modified by LLM (iteration 1): Handle base cases */
  else {
    assert a.Length <= 1;
    if a.Length == 0 {
      assert sorted(a[..]);
    } else {
      assert a.Length == 1;
      assert sorted(a[..]);
    }
  }
}

//IMPL sortAux
method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  /* code modified by LLM (iteration 1): Added decreases clause for termination */
  decreases r - l
{
  if r - l > 1 {
    var m := l + (r - l) / 2;
    /* code modified by LLM (iteration 1): Establish preconditions */
    assert l < m < r;
    assert 0 <= l < m <= a.Length;
    assert 0 <= m < r <= a.Length;
    
    /* code modified by LLM (iteration 1): First recursive call */
    sortAux(a, l, m);
    assert sorted(a[l..m]);
    assert a[..l] == old(a[..l]);
    
    /* code modified by LLM (iteration 1): Second recursive call with proper state tracking */
    ghost var a_mid := a[..];
    sortAux(a, m, r);
    assert sorted(a[m..r]);
    assert a[..l] == old(a[..l]);
    assert a[l..m] == a_mid[l..m];
    assert sorted(a[l..m]);
    
    /* code modified by LLM (iteration 1): Establish merge preconditions */
    assert 0 <= l < m < r <= a.Length;
    assert sorted(a[l..m]) && sorted(a[m..r]);
    
    mergeArr(a, l, m, r);
  }
  /* code modified by LLM (iteration 1): Base case */
  else {
    assert r - l <= 1;
    assert sorted(a[l..r]);
  }
}