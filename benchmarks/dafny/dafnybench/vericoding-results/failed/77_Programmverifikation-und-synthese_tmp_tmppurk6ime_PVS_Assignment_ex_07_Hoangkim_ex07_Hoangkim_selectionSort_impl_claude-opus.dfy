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
lemma SortedSubsequence(a: seq<int>, i: nat, j: nat)
    requires 0 <= i <= j <= |a|
    requires sorted(a)
    ensures sorted(a[i..j])
{
    if i < j {
        assert forall k | i < k < j :: a[k-1] <= a[k];
    }
}

lemma SwapMultiset(a: seq<int>, i: nat, j: nat)
    requires 0 <= i < |a| && 0 <= j < |a|
    ensures multiset(a[i := a[j]][j := a[i]]) == multiset(a)
{
    var swapped := a[i := a[j]][j := a[i]];
    if i == j {
        assert swapped == a;
    } else {
        assert multiset(swapped) == multiset(a);
    }
}

lemma SortedExtend(a: seq<int>, i: nat)
    requires 0 < i < |a|
    requires sorted(a[..i])
    requires forall k | 0 <= k < i :: a[k] <= a[i]
    ensures sorted(a[..i+1])
{
    assert forall k | 0 < k < i+1 :: a[k-1] <= a[k];
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
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i < a.Length
        invariant sorted(a[..i])
        invariant forall x, y | 0 <= x < i <= y < a.Length :: a[x] <= a[y]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var minIdx := FindMin(a, i);
        assert i <= minIdx < a.Length;
        assert forall x :: i <= x < a.Length ==> a[minIdx] <= a[x];
        
        if minIdx != i {
            var temp := a[i];
            a[i] := a[minIdx];
            a[minIdx] := temp;
            SwapMultiset(a[..], i, minIdx);
        }
        
        assert forall k | 0 <= k < i :: a[k] <= a[i];
        if i > 0 {
            SortedExtend(a[..], i);
        }
        
        i := i + 1;
    }
    
    assert i == a.Length - 1;
    assert sorted(a[..i]);
    assert sorted(a[..]);
}
// </vc-code>

//Problem03