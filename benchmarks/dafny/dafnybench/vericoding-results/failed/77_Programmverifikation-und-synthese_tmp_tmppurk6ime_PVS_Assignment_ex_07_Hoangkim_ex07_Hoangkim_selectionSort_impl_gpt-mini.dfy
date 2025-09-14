//Problem01
//a)

//b)
//Problem04

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  assume{:axiom} false;
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

// <vc-helpers>
method FindMinAux(a: array?<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  var m := lo;
  var k := lo + 1;
  while k < a.Length
    invariant lo <= m < a.Length
    invariant lo + 1 <= k <= a.Length
    invariant forall x :: lo <= x < k ==> a[m] <= a[x]
    decreases a.Length - k
  {
    if a[k] < a[m] {
      m := k;
    }
    k := k + 1;
  }
  minIdx := m;
}
// </vc-helpers>

// <vc-spec>
method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var min := i;
    var k := i + 1;
    while k < n
      invariant i <= min < n
      invariant i + 1 <= k <= n
      invariant forall x :: i <= x < k ==> a[min] <= a[x]
      decreases n - k
    {
      if a[k] < a[min] {
        min := k;
      }
      k := k + 1;
    }
    var tmp := a[i];
    a[i] := a[min];
    a[min] := tmp;
    i := i + 1;
  }
}
// </vc-code>

//Problem03