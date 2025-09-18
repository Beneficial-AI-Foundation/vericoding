// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper predicate `IsFirstDuplicate` is designed to verify if a given value `val` is indeed the 'first duplicate' according to the problem's definition. The definition of 'first duplicate' is that for any other duplicate `(lst[k], lst[l])` where `l < j` (meaning it appears earlier in the sequence), the value `lst[k]` must not be `val`. The previous version of the helper was slightly off by not correctly capturing this condition regarding other duplicates existing earlier in the sequence. It's not enough to check that all other duplicates appear after `(i, j)`. It must ensure no other duplicates appear before `i`. */
predicate IsFirstDuplicate(lst: seq<int>, val: int)
    requires exists i, j :: 0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == val
{
    exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == val &&
    
    // forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i
    // The original ensures clause definition for FirstDuplicate: 
    // (result != -1 ==> exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
    // forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
    
    // This part should match the 'forall' in the ensures clause.
    // means that if there's any other duplicate pair (k, l) with l <= i, then k must also be >= i.
    // This means that the 'i' for our 'val' is the smallest possible start index for any duplicate.
    forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i
    )
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
/* code modified by LLM (iteration 5): The logic for finding the first duplicate array was refined based on the `ensures` clause which primarily defines the `first duplicate`. The definition of the `first duplicate` focuses on identifying a duplicate `val` such that its first occurrence in a pair `(i,j)` makes `i` the smallest possible start index for a duplicate. The original code was identifying the duplicate with the smallest `j`. To align with the updated `ensures` clause, the code now searches for the `duplicate_value` where its first index `i` is the minimum across all possible duplicates in the sequence. This ensures to find the correct duplicate matching the new `ensures` clause which checks `l <= i ==> k >= i`. */
{
    if |lst| <= 1 {
        result := -1;
        return;
    }

    var min_i := |lst|; // Stores the smallest index `i` of a first occurrence of a duplicate
    var min_j_for_min_i := |lst|;
    var first_duplicate_val := -1;

    for i := 0 to |lst| - 2 {
        for j := i + 1 to |lst| - 1 
            //loop invariant exists k, l :: 0 <= k < l < |lst| && lst[k] == lst[l]
            //loop invariant min_i holds the minimum i index encountered for a duplicate pair
            //loop invariant first_duplicate_val is the value at min_i
        {
            if lst[i] == lst[j] {
                if i < min_i {
                    min_i := i;
                    min_j_for_min_i := j;
                    first_duplicate_val := lst[i];
                } else if i == min_i && j < min_j_for_min_i {
                    min_j_for_min_i := j;
                    first_duplicate_val := lst[i];
                }
            }
        }
    }

    result := first_duplicate_val;

    // Assert the condition from the ensures clause to help the verifier
    if result != -1 {
        assert exists i_idx, j_idx :: (0 <= i_idx < j_idx < |lst| && lst[i_idx] == lst[j_idx] && lst[i_idx] == first_duplicate_val &&
               forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i_idx ==> k >= i_idx);
    }
}
// </vc-code>
