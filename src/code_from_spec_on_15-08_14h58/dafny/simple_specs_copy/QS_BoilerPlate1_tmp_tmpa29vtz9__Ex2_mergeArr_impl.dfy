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


//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//IMPL Ex2

/* code modified by LLM (iteration 4): Fixed invariants about element containment and ordering conditions */
method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  var left := copyArr(a, l, m);
  var right := copyArr(a, m, r);
  
  var i := 0;
  var j := 0;
  var k := l;
  
  while i < left.Length && j < right.Length
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant k == l + i + j
    invariant l <= k <= r
    invariant sorted(a[l..k])
    invariant i < left.Length && j < right.Length && k > l ==> a[k-1] <= left[i] && a[k-1] <= right[j]
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant left[..] == old(a[l..m])
    invariant right[..] == old(a[m..r])
    invariant sorted(left[..]) && sorted(right[..])
    invariant multiset(a[l..k]) == multiset(left[..i]) + multiset(right[..j])
  {
    if left[i] <= right[j] {
      a[k] := left[i];
      i := i + 1;
    } else {
      a[k] := right[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  while i < left.Length
    invariant 0 <= i <= left.Length
    invariant j == right.Length
    invariant k == l + i + j
    invariant l <= k <= r
    invariant sorted(a[l..k])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant left[..] == old(a[l..m])
    invariant sorted(left[..])
    invariant k > l ==> (i < left.Length ==> a[k-1] <= left[i])
    invariant multiset(a[l..k]) == multiset(left[..i]) + multiset(right[..])
  {
    a[k] := left[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < right.Length
    invariant i == left.Length
    invariant 0 <= j <= right.Length
    invariant k == l + i + j
    invariant l <= k <= r
    invariant sorted(a[l..k])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant right[..] == old(a[m..r])
    invariant sorted(right[..])
    invariant k > l ==> (j < right.Length ==> a[k-1] <= right[j])
    invariant multiset(a[l..k]) == multiset(left[..]) + multiset(right[..j])
  {
    a[k] := right[j];
    j := j + 1;
    k := k + 1;
  }
}