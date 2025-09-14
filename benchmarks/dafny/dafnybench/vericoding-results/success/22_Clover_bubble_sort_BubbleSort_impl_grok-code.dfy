

// <vc-helpers>
predicate SortedRange(a: array<int>, lo: int, hi: int)
  reads a
{
  0 <= lo <= hi <= a.Length && forall i,j::lo <= i < j < hi ==> a[i] <= a[j]
}

predicate PrefixLeSuffix(a: array<int>, pos: int)
  reads a
{
  0 <= pos <= a.Length && forall i,j::0 <= i < pos <= j < a.Length ==> a[i] <= a[j]
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n <= 1 { return; }
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant SortedRange(a, n - i, n)
    invariant PrefixLeSuffix(a, n - i)
  {

    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant SortedRange(a, n - i, n)
      invariant PrefixLeSuffix(a, n - i)
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
    {
      if a[j] > a[j+1] {
        var temp := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

