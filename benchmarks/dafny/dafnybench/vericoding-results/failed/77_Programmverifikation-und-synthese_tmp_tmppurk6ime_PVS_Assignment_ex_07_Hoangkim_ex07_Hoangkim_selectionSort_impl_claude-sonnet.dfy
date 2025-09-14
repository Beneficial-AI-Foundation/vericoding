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
lemma FindMinCorrectness(a: array<int>, lo: nat, minIdx: nat)
    requires a.Length > 0 && lo < a.Length
    requires lo <= minIdx < a.Length
    requires forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
}

lemma SortedPreservation(a: array<int>, i: nat)
    requires i < a.Length
    requires forall k :: 0 <= k < i ==> (forall j :: k < j < a.Length ==> a[k] <= a[j])
    requires forall k :: 0 < k < i ==> a[k-1] <= a[k]
    ensures forall k :: 0 < k < i+1 ==> a[k-1] <= a[k]
{
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
    if a.Length == 0 {
        return;
    }
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> (forall j :: k < j < a.Length ==> a[k] <= a[j])
        invariant forall k :: 0 < k < i ==> a[k-1] <= a[k]
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