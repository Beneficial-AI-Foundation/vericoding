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

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  /* code modified by LLM (iteration 3): store original array sections for preservation */
  var old_prefix := a[..l];
  var old_suffix := a[r..];
  var old_left := a[l..m];
  var old_right := a[m..r];
  
  var temp := new int[r - l];
  var i := l;
  var j := m;
  var k := 0;
  
  /* code modified by LLM (iteration 3): fix merge loop with strengthened sorted invariant */
  while k < r - l
    invariant 0 <= k <= r - l
    invariant l <= i <= m
    invariant m <= j <= r
    invariant k == (i - l) + (j - m)
    invariant sorted(temp[..k])
    invariant i == m || j == r || (i < m && j < r)
    invariant sorted(a[l..m]) && sorted(a[m..r])
    invariant a[l..m] == old_left && a[m..r] == old_right
    invariant forall x, y :: 0 <= x < y < k ==> temp[x] <= temp[y]
    invariant forall x :: 0 <= x < k && i < m ==> temp[x] <= a[i]
    invariant forall x :: 0 <= x < k && j < r ==> temp[x] <= a[j]
  {
    if i < m && (j >= r || a[i] <= a[j]) {
      temp[k] := a[i];
      i := i + 1;
    } else {
      temp[k] := a[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 3): copy back with corrected invariants */
  k := 0;
  while k < r - l
    invariant 0 <= k <= r - l
    invariant forall x :: 0 <= x < l ==> a[x] == old_prefix[x]
    invariant forall x :: r <= x < a.Length ==> a[x] == old_suffix[x - r]
    invariant a[l..l+k] == temp[..k]
    invariant sorted(temp[..])
    invariant forall x :: l+k <= x < r ==> (x < m ==> a[x] == old_left[x-l]) && (x >= m ==> a[x] == old_right[x-m])
  {
    a[l + k] := temp[k];
    k := k + 1;
  }
}