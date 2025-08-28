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
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  minIdx := lo;
  var i := lo + 1;
  
  while i < a.Length
    invariant lo <= minIdx < a.Length
    invariant lo <= i <= a.Length
    invariant forall x :: lo <= x < i ==> a[minIdx] <= a[x]
  {
    if a[i] < a[minIdx] {
      minIdx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
