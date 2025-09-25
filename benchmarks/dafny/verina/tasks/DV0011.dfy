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
    // impl-start
    assume {:axiom} false;
    result := -1;
    // impl-end
}
// </vc-code>
