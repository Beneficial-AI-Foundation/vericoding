predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a
  requires a != null && from <= to && to <= a.Length
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a
  requires a != null
{
  sorted_between (a, 0, a.Length)
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while (i < a.Length - 1)
    invariant 0 <= i <= a.Length - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant sorted_between(a, a.Length - i, a.Length)
    invariant if i > 0 then forall u :: 0 <= u < a.Length - i ==> a[u] <= a[a.Length - i]
  {
    var j := 0;
    while (j < a.Length - i - 1)
      invariant 0 <= j <= a.Length - i - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted_between(a, a.Length - i, a.Length)
      invariant if i > 0 then forall u :: 0 <= u < a.Length - i ==> a[u] <= a[a.Length - i]
    {
      if (a[j] > a[j+1])
      {
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

