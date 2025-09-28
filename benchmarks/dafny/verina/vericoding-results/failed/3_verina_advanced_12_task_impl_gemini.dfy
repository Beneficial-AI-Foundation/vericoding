// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): providing a standard predicate to check for duplicates in a prefix */
predicate NoDuplicatesInPrefix(lst: seq<int>, n: nat)
    requires n <= |lst|
{
    forall k, l :: 0 <= k < l < n ==> lst[k] != lst[l]
}
// </vc-helpers>

// <vc-spec>
method FirstDuplicate(lst: seq<int>) returns (result: int)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
            forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented a standard nested loop approach with correct invariants to find the first duplicate */
    var j: nat := 0;
    while j < |lst|
        invariant 0 <= j <= |lst|
        invariant NoDuplicatesInPrefix(lst, j)
    {
        var i: nat := 0;
        while i < j
            invariant 0 <= i <= j
            invariant forall k :: 0 <= k < i ==> lst[k] != lst[j]
        {
            if lst[i] == lst[j] {
                result := lst[j];
                return;
            }
            i := i + 1;
        }
        j := j + 1;
    }
    result := -1;
}
// </vc-code>
