// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add decreases clause to fix termination */
lemma SortedLemma(lst: array<int>, i: int, j: int)
    requires 0 <= i && i <= j && j < lst.Length
    requires forall k :: i <= k < j ==> lst[k] <= lst[k+1]
    ensures forall k, l :: i <= k && k <= l && l <= j ==> lst[k] <= lst[l]
    decreases j - i
{
    if i < j {
        SortedLemma(lst, i+1, j);
        assert forall k, l :: i+1 <= k && k <= l && l <= j ==> lst[k] <= lst[l];
        assert lst[i] <= lst[i+1];
    }
}
// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Simplified implementation with proper lemma usage */
{
    if lst.Length == 1 {
        result := true;
        return;
    }
    
    var index := 0;
    while index < lst.Length - 1
        invariant 0 <= index <= lst.Length - 1
        invariant forall k :: 0 <= k < index ==> lst[k] <= lst[k+1]
    {
        if lst[index] > lst[index+1] {
            result := false;
            return;
        }
        index := index + 1;
    }
    
    SortedLemma(lst, 0, lst.Length - 1);
    result := true;
}
// </vc-code>
