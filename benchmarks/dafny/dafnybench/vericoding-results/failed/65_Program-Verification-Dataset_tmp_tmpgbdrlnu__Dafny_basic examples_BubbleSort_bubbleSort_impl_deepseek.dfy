predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

// <vc-helpers>
lemma BubbleUpLemma(a: array<int>, to: int)
  requires a != null
  requires 0 <= to <= a.Length
  ensures to > 0 ==> pivot(a, to, to - 1)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if to == 0 {
    return;
  }
  
  ghost var oldA := a[..];
  
  var i := 0;
  while i < to - 1
    invariant 0 <= i <= to - 1
    invariant i > 0 ==> forall u, v :: 0 <= u < i < v < to ==> a[u] <= a[v]
    invariant multiset(a[..]) == multiset(oldA)
  {
    if a[i] > a[i + 1] {
      var temp := a[i];
      a[i] := a[i + 1];
      a[i + 1] := temp;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant i >= 0 ==> sorted(a, n - i - 1, n)
    invariant i >= 0 ==> forall u, v :: 0 <= u < n - i - 1 <= v < n ==> a[u] <= a[v]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    BubbleUpLemma(a, n - i);
    i := i + 1;
  }
}
// </vc-code>

