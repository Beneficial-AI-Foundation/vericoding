//Problem01
//a)

//b)
//Problem04

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}



//Problem03

// <vc-helpers>
{:allow_warnings}
module AllowWarnings {}
// </vc-helpers>

// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := lo + 1;
  var min := lo;
  while i < n
    invariant lo <= min < n
    invariant lo <= i && i <= n
    invariant forall x :: lo <= x < i ==> a[min] <= a[x]
    decreases n - i
  {
    if a[i] < a[min] {
      min := i;
    }
    i := i + 1;
  }
  minIdx := min;
}
// </vc-code>

