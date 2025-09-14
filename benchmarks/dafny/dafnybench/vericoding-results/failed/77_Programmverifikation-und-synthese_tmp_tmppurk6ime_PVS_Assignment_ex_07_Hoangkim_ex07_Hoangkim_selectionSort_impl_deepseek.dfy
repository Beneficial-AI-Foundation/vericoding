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
ghost predicate sortedSeq(a:seq<int>)
{
    if |a| == 0 then true else
        forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    minIdx := lo;
    var idx: nat := lo + 1;
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

lemma FindMinLemma(a: array<int>, lo: nat, minIdx: nat)
    requires a != null
    requires a.Length > 0 && lo < a.Length
    requires lo <= minIdx < a.Length
    requires forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
    ensures multiset(a[..]) == multiset(old(a[..]))
{
}

lemma SwapLemma(a: array<int>, i: nat, j: nat)
    requires a != null
    requires i < a.Length && j < a.Length
    ensures multiset(a[..]) == multiset(old(a[..]))
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
    var i: nat := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant i > 0 ==> sortedSeq(a[..i])
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall k, l :: 0 <= k < i && i <= l < a.Length ==> a[k] <= a[l]
    {
        var minIdx: nat;
        minIdx := FindMin(a, i);
        FindMinLemma(a, i, minIdx);
        
        if i != minIdx {
            var temp := a[i];
            a[i] := a[minIdx];
            a[minIdx] := temp;
            SwapLemma(a, i, minIdx);
        }
        
        i := i + 1;
    }
}
// </vc-code>

//Problem03