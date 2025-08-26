method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length1 - 1;
  
  while i < a.Length0 && j >= 0
    invariant 0 <= i <= a.Length0
    invariant -1 <= j < a.Length1
    invariant exists ii, jj :: 0 <= ii < a.Length0 && 0 <= jj < a.Length1 && a[ii,jj] == key
    invariant forall ii, jj :: (0 <= ii < i && 0 <= jj < a.Length1) ==> a[ii,jj] < key
    invariant forall ii, jj :: (0 <= ii < a.Length0 && j < jj < a.Length1) ==> a[ii,jj] > key
    invariant forall ii, jj :: (0 <= ii < i && j < jj < a.Length1) ==> a[ii,jj] != key
  {
    if a[i,j] == key {
      m := i;
      n := j;
      return;
    } else if a[i,j] > key {
      // Prove that all elements in column j from row i onwards are > key
      MonotonicityLemmaColumns(a, key, i, j);
      j := j - 1;
    } else {
      assert a[i,j] < key;
      // Prove that all elements in row i from column 0 to j are < key
      MonotonicityLemmaRows(a, key, i, j);
      i := i + 1;
    }
  }
  
  // This point should never be reached due to the precondition
  assert false;
}
// </vc-code>
// <vc-helpers>
lemma MonotonicityLemmaRows(a: array2<int>, key: int, i: int, j: int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires 0 <= i < a.Length0 && 0 <= j < a.Length1
  requires a[i,j] < key
  ensures forall jj :: 0 <= jj <= j ==> a[i,jj] < key
{
  forall jj | 0 <= jj <= j
    ensures a[i,jj] < key
  {
    if jj < j {
      assert a[i,jj] <= a[i,j];
      assert a[i,j] < key;
    } else {
      assert jj == j;
      assert a[i,jj] == a[i,j] < key;
    }
  }
}

lemma MonotonicityLemmaColumns(a: array2<int>, key: int, i: int, j: int)
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires 0 <= i < a.Length0 && 0 <= j < a.Length1
  requires a[i,j] > key
  ensures forall ii :: i <= ii < a.Length0 ==> a[ii,j] > key
{
  forall ii | i <= ii < a.Length0
    ensures a[ii,j] > key
  {
    if ii > i {
      assert a[i,j] <= a[ii,j];
      assert a[i,j] > key;
    } else {
      assert ii == i;
      assert a[ii,j] == a[i,j] > key;
    }
  }
}
// </vc-helpers>