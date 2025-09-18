// <vc-preamble>
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish
{
    // impl-start
    assume {:axiom} false;
    result := start;
    // impl-end
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == old(a[j])) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[j] == old(a[i])) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariants for SelectionSort by adjusting the first loop's invariants relating to multisets and deleting the second loop's multiset invariant entirely, as it was redundant. Also, the FindMinIndexInRange method from the preamble needed to be utilized, so the method was passed to the implementation to fix the verification issues related to it. */
{
    result := new int[a.Length];
    if a.Length == 0 {
        return result;
    }

    var b := new int[a.Length];
    // Copy contents of 'a' to 'b'
    var k := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall l :: 0 <= l < k ==> b[l] == a[l]
        invariant multiset(b[0 .. k]) + multiset(a[k ..]) == multiset(a[..])
    {
        b[k] := a[k];
        k := k + 1;
    }

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall l, m :: 0 <= l <= m < i ==> b[l] <= b[m]
        invariant multiset(b[..]) == multiset(old(a[..]))
        invariant forall l :: i <= l < a.Length ==> (forall m :: 0 <= m < i ==> b[m] <= b[l])
    {
        var minIndex := FindMinIndexInRange(b, i, a.Length);
        Swap(b, i, minIndex);
        i := i + 1;
    }
    result := b;
}
// </vc-code>
