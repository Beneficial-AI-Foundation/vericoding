// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed postcondition proof for first duplicate */
    result := -1;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant result == -1
        invariant forall k, l :: 0 <= k < l < i ==> lst[k] != lst[l]
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> lst[k] != lst[i]
        {
            if lst[j] == lst[i] {
                result := lst[i];
                assert 0 <= j < i < |lst|;
                assert lst[j] == lst[i] == result;
                assert forall p, q :: 0 <= p < q < i ==> lst[p] != lst[q];
                assert forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= j;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
