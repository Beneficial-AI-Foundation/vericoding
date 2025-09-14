

// <vc-helpers>
lemma PreserveAfterColDecrease(a: array2<int>, i: int, j: int, key: int)
  requires 0 <= i < a.Length0
  requires 0 <= j < a.Length1
  requires forall ii, jj, jj' :: 0 <= ii < a.Length0 && 0 <= jj < jj' < a.Length1 ==> a[ii,jj] <= a[ii,jj']
  requires forall ii, ii', jj :: 0 <= ii < ii' < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] <= a[ii',jj]
  requires exists ii, jj :: i <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key
  requires a[i,j] > key
  ensures exists ii, jj :: i <= ii < a.Length0 && 0 <= jj <= j-1 && a[ii,jj] == key
{
  var ii, jj :| i <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key;
  if jj == j {
    // then a[ii,j] == key, and ii >= i
    if ii == i {
      // then a[i,j] == key contradicts a[i,j] > key
      assert a[ii,jj] == key;
      assert a[i,j] == a[ii,jj];
      assert false;
    } else {
      // ii > i, by row monotonicity a[i,j] <= a[ii,j] == key contradicts a[i,j] > key
      assert ii > i;
      // instantiate monotonicity: since i < ii and 0<=j<a.Length1
      assert a[i,j] <= a[ii,j];
      assert a[ii,j] == key;
      assert a[i,j] <= key;
      assert false;
    }
  } else {
    // jj < j, so jj <= j-1 and can be used as witness
    assert 0 <= jj <= j-1;
    assert exists ii0, jj0 :: ii0 == ii && jj0 == jj && i <= ii0 < a.Length0 && 0 <= jj0 <= j-1 && a[ii0,jj0] == key;
  }
}

lemma PreserveAfterRowIncrease(a: array2<int>, i: int, j: int, key: int)
  requires 0 <= i < a.Length0
  requires 0 <= j < a.Length1
  requires forall ii, jj, jj' :: 0 <= ii < a.Length0 && 0 <= jj < jj' < a.Length1 ==> a[ii,jj] <= a[ii,jj']
  requires forall ii, ii', jj :: 0 <= ii < ii' < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] <= a[ii',jj]
  requires exists ii, jj :: i <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key
  requires a[i,j] < key
  ensures exists ii, jj :: i+1 <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key
{
  var ii, jj :| i <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key;
  if ii == i {
    // then a[i,jj] == key, but a[i,jj] <= a[i,j] < key, contradiction
    assert a[ii,jj] == key;
    assert jj <= j;
    // since jj <= j, by row monotonicity of columns we have a[i,jj] <= a[i,j]
    if jj < j {
      // instantiate column monotonicity: for jj < j, a[i,jj] <= a[i,j]
      assert a[i,jj] <= a[i,j];
      assert a[i,jj] == key;
      assert a[i,j] >= a[i,jj];
      assert a[i,j] >= key;
      assert false;
    } else {
      // jj == j: then a[i,j] == key contradicts a[i,j] < key
      assert a[i,j] == key;
      assert false;
    }
  } else {
    // ii > i, so ii >= i+1 and can be used as witness
    assert ii >= i+1;
    assert exists ii0, jj0 :: ii0 == ii && jj0 == jj && i+1 <= ii0 < a.Length0 && 0 <= jj0 <= j && a[ii0,jj0] == key;
  }
}
// </vc-helpers>

// <vc-spec>
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
    invariant exists ii, jj :: i <= ii < a.Length0 && 0 <= jj <= j && a[ii,jj] == key
    decreases (a.Length0 - i) + j
  {
    // indexing is safe because of the loop condition and invariants
    var v := a[i,j];
    if v == key {
      return i, j;
    }
    if v > key {
      // eliminate column j
      PreserveAfterColDecrease(a, i, j, key);
      j := j - 1;
    } else {
      // v < key, eliminate row i
      PreserveAfterRowIncrease(a, i, j, key);
      i := i + 1;
    }
  }
  // Because of the precondition that the key exists somewhere, loop cannot exit normally.
  // But to satisfy verifier, return some valid indices (this point is unreachable).
  return 0, 0;
}
// </vc-code>

