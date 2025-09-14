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
ghost predicate sorted(a: seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}
// </vc-helpers>

// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
// </vc-spec>
// <vc-code>
{
  minIdx := lo;
  var idx := lo + 1;
  
  while idx < a.Length
    invariant lo <= minIdx < a.Length
    invariant lo <= idx <= a.Length
    invariant forall x :: lo <= x < idx ==> a[minIdx] <= a[x]
  {
    if a[idx] < a[minIdx] {
      minIdx := idx;
    }
    idx := idx + 1;
  }
}
// </vc-code>

