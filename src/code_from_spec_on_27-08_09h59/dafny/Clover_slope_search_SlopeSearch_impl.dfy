// <vc-helpers>
lemma PreservationLemma(a: array2<int>, key: int, m: int, n: int, m': int, n': int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires 0 <= m < a.Length0 && 0 <= n < a.Length1
  requires forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] < key
  requires forall i,j :: 0 <= i < a.Length0 && n < j < a.Length1 ==> a[i,j] > key
  requires a[m,n] < key && m' == m + 1 && n' == n
  ensures forall i,j :: 0 <= i < m' && 0 <= j < a.Length1 ==> a[i,j] < key
{
  forall i,j | 0 <= i < m' && 0 <= j < a.Length1
    ensures a[i,j] < key
  {
    if i < m {
      assert a[i,j] < key;
    } else {
      assert i == m;
      assert a[i,j] == a[m,j];
      if j <= n {
        assert a[m,j] <= a[m,n] < key;
      } else {
        assert a[m,j] > key;
      }
    }
  }
}

lemma PreservationLemma2(a: array2<int>, key: int, m: int, n: int, m': int, n': int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires 0 <= m < a.Length0 && 0 <= n < a.Length1
  requires forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] < key
  requires forall i,j :: 0 <= i < a.Length0 && n < j < a.Length1 ==> a[i,j] > key
  requires a[m,n] > key && m' == m && n' == n - 1
  ensures forall i,j :: 0 <= i < a.Length0 && n' < j < a.Length1 ==> a[i,j] > key
{
  forall i,j | 0 <= i < a.Length0 && n' < j < a.Length1
    ensures a[i,j] > key
  {
    if j > n {
      assert a[i,j] > key;
    } else {
      assert j == n;
      assert a[i,j] == a[i,n];
      if i >= m {
        assert a[i,n] >= a[m,n] > key;
      } else {
        assert a[i,n] < key;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  m := 0;
  n := a.Length1 - 1;
  
  while m < a.Length0 && n >= 0
    invariant 0 <= m <= a.Length0
    invariant -1 <= n < a.Length1
    invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] < key
    invariant forall i,j :: 0 <= i < a.Length0 && n < j < a.Length1 ==> a[i,j] > key
    invariant exists i,j :: m <= i < a.Length0 && 0 <= j <= n && a[i,j] == key
  {
    if a[m,n] == key {
      return;
    } else if a[m,n] < key {
      PreservationLemma(a, key, m, n, m + 1, n);
      m := m + 1;
    } else {
      PreservationLemma2(a, key, m, n, m, n - 1);
      n := n - 1;
    }
  }
}
// </vc-code>
