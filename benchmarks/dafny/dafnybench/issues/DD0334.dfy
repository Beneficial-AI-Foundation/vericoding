// <vc-preamble>
// Sorts array 'a' using the insertion sort algorithm.
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length 
        decreases a.Length - i 
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            decreases j
            invariant 0 <= j <= i 
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant forall l, r :: 0 <= l < r <= i && r != j ==> a[l] <= a[r]
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}
// </vc-code>

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Simple test case to check the postcondition