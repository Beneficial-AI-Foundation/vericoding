// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSortedPredicate(lst: array<int>)
    reads lst
{
    forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
}

lemma SortedImpliesNoViolation(lst: array<int>)
    requires lst.Length >= 1
    requires IsSortedPredicate(lst)
    ensures forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
{
}

lemma UnsortedImpliesViolationExists(lst: array<int>)
    requires lst.Length >= 1
    requires !IsSortedPredicate(lst)
    ensures exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
{
}
// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < lst.Length - 1
        invariant 0 <= i <= lst.Length - 1
        invariant forall x, y :: 0 <= x && x < y && y <= i ==> lst[x] <= lst[y]
    {
        if lst[i] > lst[i + 1] {
            result := false;
            return;
        }
        i := i + 1;
    }
    result := true;
}
// </vc-code>
