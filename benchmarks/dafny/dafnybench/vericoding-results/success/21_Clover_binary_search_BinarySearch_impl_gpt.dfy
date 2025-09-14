

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  ensures 0<= n <=a.Length
  ensures forall i :: 0<= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i :: n<= i < a.Length ==> a[i]>=key
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] >= key
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid;
    assert mid < hi;
    assert 0 <= lo;
    assert 0 <= mid < a.Length;

    if a[mid] < key {
      // prove all indices up to mid are < key
      forall i | 0 <= i <= mid
        ensures a[i] < key
      {
        if i < mid {
          assert 0 <= i < mid < a.Length;
          assert a[i] <= a[mid];
          assert a[i] < key;
        } else {
          assert i == mid;
          assert a[i] == a[mid];
          assert a[i] < key;
        }
      }
      assert hi - (mid + 1) < hi - lo;
      lo := mid + 1;
      assert lo <= hi;
    } else {
      // prove all indices from mid to end are >= key
      forall i | mid <= i < a.Length
        ensures a[i] >= key
      {
        if i == mid {
          assert a[i] == a[mid];
          assert a[i] >= key;
        } else {
          assert 0 <= mid < i < a.Length;
          assert a[mid] <= a[i];
          assert a[i] >= a[mid];
          assert a[i] >= key;
        }
      }
      assert mid - lo < hi - lo;
      hi := mid;
      assert lo <= hi;
    }
  }
  n := lo;
}
// </vc-code>

