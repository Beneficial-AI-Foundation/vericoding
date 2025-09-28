// <vc-preamble>

function count_mismatched_pairs(arr: seq<int>): int
{
    count_mismatched_pairs_up_to(arr, |arr| / 2)
}

function count_mismatched_pairs_up_to(arr: seq<int>, limit: int): int
    requires 0 <= limit <= |arr| / 2
{
    if limit == 0 then 0
    else 
        (if arr[limit-1] != arr[|arr| - limit] then 1 else 0) + 
        count_mismatched_pairs_up_to(arr, limit - 1)
}

predicate can_make_palindromic_with_changes(arr: seq<int>, num_changes: int)
{
    num_changes >= 0 && num_changes >= count_mismatched_pairs(arr)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proves bounds for count_mismatched_pairs_up_to */
lemma LemmaCountMismatchedBounds(arr: seq<int>, limit: int)
    requires 0 <= limit <= |arr| / 2
    ensures 0 <= count_mismatched_pairs_up_to(arr, limit) <= limit
{
    if limit > 0 {
        LemmaCountMismatchedBounds(arr, limit - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method smallest_change(arr: seq<int>) returns (changes: int)
    ensures changes >= 0
    ensures changes <= |arr| / 2
    ensures changes == count_mismatched_pairs(arr)
    ensures (|arr| <= 1) ==> (changes == 0)
    ensures forall c :: 0 <= c < changes ==> !can_make_palindromic_with_changes(arr, c)
    ensures can_make_palindromic_with_changes(arr, changes)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added lemma call to prove postconditions */
    changes := 0;
    var i := 0;
    var n := |arr|;
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant changes == count_mismatched_pairs_up_to(arr, i)
    {
        if arr[i] != arr[n - 1 - i] {
            changes := changes + 1;
        }
        i := i + 1;
    }
    LemmaCountMismatchedBounds(arr, n / 2);
}
// </vc-code>
