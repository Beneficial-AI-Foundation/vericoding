predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
lemma SortedLemma(a: array?<int>, l:int, u:int, i:int, j:int)
  requires a != null
  requires sorted(a, l, u)
  requires 0 <= l <= i <= j <= u < a.Length
  ensures a[i] <= a[j]
{
  assert sorted(a, l, u);
  assert a[i] <= a[j];
}

lemma AllLeftLessForKeyAt(a: array?<int>, mid:int, key:int)
  requires a != null
  requires sorted(a, 0, a.Length - 1)
  requires 0 <= mid < a.Length
  requires a[mid] < key
  ensures forall k :: 0 <= k <= mid ==> a[k] < key
{
  forall k | 0 <= k <= mid
    ensures a[k] < key
  {
    assert mid <= a.Length - 1;
    SortedLemma(a, 0, a.Length - 1, k, mid);
    assert a[k] <= a[mid];
    assert a[mid] < key;
    assert a[k] < key;
  }
}

lemma AllRightGreaterForKeyAt(a: array?<int>, mid:int, key:int)
  requires a != null
  requires sorted(a, 0, a.Length - 1)
  requires 0 <= mid < a.Length
  requires a[mid] > key
  ensures forall k :: mid <= k < a.Length ==> a[k] > key
{
  forall k | mid <= k < a.Length
    ensures a[k] > key
  {
    assert k <= a.Length - 1;
    SortedLemma(a, 0, a.Length - 1, mid, k);
    assert a[mid] <= a[k];
    assert a[mid] > key;
    assert a[k] > key;
  }
}

lemma NoKeyFromSplit(a: array?<int>, key:int, lo:int, hi:int)
  requires a != null
  requires 0 <= lo <= hi + 1 <= a.Length
  requires forall k :: 0 <= k < lo ==>
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// <vc-code>
lemma SortedLemma(a: array?<int>, l:int, u:int, i:int, j:int)
  requires a != null
  requires sorted(a, l, u)
  requires 0 <= l <= i <= j <= u < a.Length
  ensures a[i] <= a[j]
{
  assert sorted(a, l, u);
  assert a[i] <= a[j];
}

lemma AllLeftLessForKeyAt(a: array?<int>, mid:int, key:int)
  requires a != null
  requires sorted(a, 0, a.Length - 1)
  requires 0 <= mid < a.Length
  requires a[mid] < key
  ensures forall k :: 0 <= k <= mid ==> a[k] < key
{
  forall k | 0 <= k <= mid
    ensures a[k] < key
  {
    assert mid <= a.Length - 1;
    SortedLemma(a, 0, a.Length - 1, k, mid);
    assert a[k] <= a[mid];
    assert a[mid] < key;
    assert a[k] < key;
  }
}

lemma AllRightGreaterForKeyAt(a: array?<int>, mid:int, key:int)
  requires a != null
  requires sorted(a, 0, a.Length - 1)
  requires 0 <= mid < a.Length
  requires a[mid] > key
  ensures forall k :: mid <= k < a.Length ==> a[k] > key
{
  forall k | mid <= k < a.Length
    ensures a[k] > key
  {
    assert k <= a.Length - 1;
    SortedLemma(a, 0, a.Length - 1, mid, k);
    assert a[mid] <= a[k];
    assert a[mid] > key;
    assert a[k] > key;
  }
}

lemma NoKeyFromSplit(a: array?<int>, key:int, lo:int, hi:int)
  requires a != null
  requires 0 <= lo <= hi + 1 <= a.Length
  requires forall k :: 0 <= k < lo ==>
// </vc-code>

