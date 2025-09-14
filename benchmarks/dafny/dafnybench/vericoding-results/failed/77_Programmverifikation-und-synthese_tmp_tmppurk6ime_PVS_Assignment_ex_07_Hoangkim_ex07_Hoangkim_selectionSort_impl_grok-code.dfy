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
ghost predicate sorted(a: seq<int>) {
    forall i | 0 < i < |a| :: a[i-1] <= a[i]
}

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    minIdx := lo;
    var i := lo + 1;
    while i < a.Length
        decreases a.Length - i
    {
        if a[i] < a[minIdx] {
            minIdx := i;
        }
        i := i + 1;
    }
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
    var i := 0;
    while i < a.Length - 1
        decreases a.Length - i
        invariant 0 <= i <= a.Length
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant sorted(a[..i])
        invariant forall x, j :: 0 <= x < i && i <= j < a.Length ==> a[x] <= a[j]
    {
        var minIdx := FindMin(a, i);
        var temp := a[i];
        a[i] := a[minIdx];
        a[minIdx] := temp;
        i := i + 1;
    }
}
// </vc-code>

//Problem03