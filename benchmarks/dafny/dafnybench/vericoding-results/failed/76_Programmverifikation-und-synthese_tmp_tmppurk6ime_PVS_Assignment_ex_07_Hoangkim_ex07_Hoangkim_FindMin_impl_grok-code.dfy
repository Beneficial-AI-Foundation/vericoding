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
// Helpers is empty so far - still empty
// </vc-helpers>

// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
// </vc-spec>
// <vc-code>
minIdx := lo;
    var i: nat := lo +1;
    while i <= a.Length - 1
        invariant lo <= minIdx < a.Length
        invariant forall k: nat :: lo <= k < i ==> a[minIdx] <= a[k]
        decreases a.Length - i
    {
        if a[i] < a[minIdx] {
            minIdx := i;
        }
        i := i + 1;
    }
// </vc-code>

