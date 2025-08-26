method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]

<vc-code>
{
  if n == 0 {
    return true;
  }
  
  var i := 0;
  var j := 0;
  
  while i < n && j < m
    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < i ==> v[k] in w[..m]
    invariant i < n ==> forall k :: 0 <= k < j ==> w[k] < v[i]
  {
    if v[i] == w[j] {
      i := i + 1;
      j := j + 1;
    } else if v[i] > w[j] {
      j := j + 1;
    } else {
      // v[i] < w[j], and since arrays are strictly sorted
      // v[i] cannot be found in w[j..m], so not in w[..m]
      assert v[i] < w[j];
      StrictSortedImpliesMonotonic(w[..], j, m);
      assert forall k :: j <= k < m ==> v[i] < w[k];
      assert v[i] !in w[j..m];
      SeqConcatProperty(w[..], j, m);
      assert v[i] !in w[..j];
      assert v[i] !in w[..m];
      return false;
    }
  }
  
  // After the loop, either i == n (all elements found) or j == m (ran out of w elements)
  if i == n {
    return true;
  } else {
    // i < n && j == m, so we didn't find v[i] in w[..m]
    assert j == m;
    assert i < n;
    assert forall k :: 0 <= k < j ==> w[k] < v[i];
    assert forall k :: 0 <= k < m ==> w[k] < v[i];
    assert v[i] !in w[..m];
    assert !(forall k :: 0 <= k < n ==> v[k] in w[..m]);
    return false;
  }
}
</vc-code>

<vc-helpers>
predicate strictSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

lemma StrictSortedImpliesMonotonic(s: seq<int>, start: int, end: int)
  requires strictSorted(s)
  requires 0 <= start < end <= |s|
  ensures forall k :: start <= k < end ==> s[start] < s[k] || k == start
{
  forall k | start <= k < end
    ensures s[start] < s[k] || k == start
  {
    if start < k {
      assert s[start] < s[k];
    }
  }
}

lemma SeqConcatProperty(s: seq<int>, mid: int, end: int)
  requires 0 <= mid <= end <= |s|
  ensures s[..end] == s[..mid] + s[mid..end]
{
  // This is automatically proven by Dafny's sequence axioms
}
</vc-helpers>