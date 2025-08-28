// <vc-helpers>
lemma MultisetPreservationAfterSwap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var oldSeq := old(a[..]);
  var newSeq := a[..];
  
  if i == j {
    assert oldSeq == newSeq;
  } else {
    assert multiset(oldSeq) == multiset(newSeq);
  }
}

lemma SortedAfterInnerLoop(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  requires forall k :: 0 <= k < n-1 ==> a[k] <= a[k+1]
  requires forall k :: n <= k < a.Length ==> (forall m :: 0 <= m < n ==> a[m] <= a[k])
  ensures forall i,j :: 0 <= i < j < a.Length && (i < n || j < n) ==> a[i] <= a[j]
{
}

lemma SortedPreservation(a: array<int>, n: int, i: int)
  requires 0 <= i <= n <= a.Length
  requires forall x :: n - i <= x < a.Length ==> (forall y :: 0 <= y < n - i ==> a[y] <= a[x])
  requires forall x,y :: n - i <= x < y < a.Length ==> a[x] <= a[y]
  ensures forall x,y :: 0 <= x < y < a.Length && (x < n - i || y < n - i) ==> a[x] <= a[y]
{
  forall x, y | 0 <= x < y < a.Length && (x < n - i || y < n - i)
    ensures a[x] <= a[y]
  {
    if x < n - i && y < n - i {
    } else if x < n - i && y >= n - i {
      assert a[x] <= a[y];
    } else if x >= n - i && y >= n - i {
      assert a[x] <= a[y];
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall x :: n - i <= x < a.Length ==> (forall y :: 0 <= y < n - i ==> a[y] <= a[x])
    invariant forall x,y :: n - i <= x < y < a.Length ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant forall x :: n - i <= x < a.Length ==> (forall y :: 0 <= y < n - i ==> a[y] <= a[x])
      invariant forall x,y :: n - i <= x < y < a.Length ==> a[x] <= a[y]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[k+1]
      invariant forall m :: j + 1 <= m < n - i ==> a[j] <= a[m]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  SortedPreservation(a, n, n);
}
// </vc-code>
