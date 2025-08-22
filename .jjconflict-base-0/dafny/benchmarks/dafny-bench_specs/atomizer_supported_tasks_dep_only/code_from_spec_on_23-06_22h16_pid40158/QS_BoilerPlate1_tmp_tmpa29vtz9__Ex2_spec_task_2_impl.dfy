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
    /* code modified by LLM (iteration 3): strengthened bounds invariant */
    invariant l + i <= a.Length
    invariant i <= ret.Length
  {
    ret[i] := a[l + i];
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): implemented multiset concatenation lemma */
lemma multisetConcat<T>(s1: seq<T>, s2: seq<T>)
  ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    multisetConcat(s1[1..], s2);
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
  }
}

/* code modified by LLM (iteration 3): implemented sorted concatenation lemma */
lemma sortedConcat(s1: seq<int>, s2: seq<int>)
  requires sorted(s1) && sorted(s2)
  requires |s1| > 0 && |s2| > 0 ==> s1[|s1|-1] <= s2[0]
  ensures sorted(s1 + s2)
{
  if |s1| == 0 || |s2| == 0 {
    return;
  }
  var combined := s1 + s2;
  forall k1, k2 | 0 <= k1 <= k2 < |combined|
    ensures combined[k1] <= combined[k2]
  {
    if k2 < |s1| {
      assert combined[k1] == s1[k1] && combined[k2] == s1[k2];
    } else if k1 >= |s1| {
      assert combined[k1] == s2[k1 - |s1|] && combined[k2] == s2[k2 - |s1|];
    } else {
      assert k1 < |s1| <= k2;
      assert combined[k1] == s1[k1] && combined[k2] == s2[k2 - |s1|];
      assert s1[k1] <= s1[|s1|-1] <= s2[0] <= s2[k2 - |s1|];
    }
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
  
  /* code modified by LLM (iteration 3): store original array content */
  ghost var originalArray := a[l..r];
  
  /* code modified by LLM (iteration 3): added multiset equality lemma call */
  multisetConcat(a[l..m], a[m..r]);
  assert multiset(a[l..r]) == multiset(a[l..m]) + multiset(a[m..r]);
  
  while i < m && j < r
    invariant l <= i <= m
    invariant m <= j <= r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(a[l..i]) + multiset(a[m..j])
    /* code modified by LLM (iteration 3): improved ordering invariants */
    invariant i < m && j < r ==> (k == 0 || temp[k-1] <= a[i]) && (k == 0 || temp[k-1] <= a[j])
    invariant i < m ==> (forall x :: x in temp[..k] ==> x <= a[i])
    invariant j < r ==> (forall x :: x in temp[..k] ==> x <= a[j])
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
    invariant l <= i <= m
    invariant j == r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(a[l..i]) + multiset(a[m..r])
    /* code modified by LLM (iteration 3): improved ordering invariant */
    invariant i < m ==> (k == 0 || temp[k-1] <= a[i])
  {
    temp[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < r
    invariant i == m
    invariant m <= j <= r
    invariant k == (i - l) + (j - m)
    invariant 0 <= k <= r - l
    invariant sorted(temp[..k])
    invariant multiset(temp[..k]) == multiset(a[l..m]) + multiset(a[m..j])
    /* code modified by LLM (iteration 3): improved ordering invariant */
    invariant j < r ==> (k == 0 || temp[k-1] <= a[j])
  {
    temp[k] := a[j];
    j := j + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 3): strengthened final assertions */
  assert k == r - l;
  assert multiset(temp[..]) == multiset(a[l..m]) + multiset(a[m..r]);
  assert multiset(temp[..]) == multiset(originalArray);
  assert sorted(temp[..]);
  
  i := 0;
  while i < r - l
    invariant 0 <= i <= r - l
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant a[l..l+i] == temp[..i]
    invariant sorted(temp[..])
    invariant multiset(temp[..]) == multiset(originalArray)
    /* code modified by LLM (iteration 3): added invariant for partial sorted property and bounds */
    invariant sorted(a[l..l+i])
    invariant i < r - l ==> (i == 0 || a[l+i-1] <= temp[i])
    invariant l + i <= a.Length
  {
    a[l + i] := temp[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 3): final proof steps */
  assert a[l..r] == temp[..];
  assert sorted(a[l..r]);
}

//ATOM sort
method sort(a : array<int>)
  ensures sorted(a[..])
  modifies a
{
  if a.Length > 1 {
    sortAux(a, 0, a.Length);
  }
}

//ATOM sortAux
method sortAux(a : array<int>, l : int, r : int)
  requires 0 <= l <= r <= a.Length
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
  decreases r - l
{
  if r - l > 1 {
    var m := l + (r - l) / 2;
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
  }
}