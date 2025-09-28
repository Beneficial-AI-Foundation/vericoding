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
lemma count_mismatched_pairs_bounds(arr: seq<int>)
    ensures count_mismatched_pairs(arr) >= 0
    ensures count_mismatched_pairs(arr) <= |arr| / 2
{
    count_mismatched_pairs_up_to_bounds(arr, |arr| / 2);
}

lemma count_mismatched_pairs_up_to_bounds(arr: seq<int>, limit: int)
    requires 0 <= limit <= |arr| / 2
    ensures count_mismatched_pairs_up_to(arr, limit) >= 0
    ensures count_mismatched_pairs_up_to(arr, limit) <= limit
{
    if limit == 0 {
        // Base case
    } else {
        count_mismatched_pairs_up_to_bounds(arr, limit - 1);
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
    /* code modified by LLM (iteration 2): added lemma call to prove bounds */
    count_mismatched_pairs_bounds(arr);
    changes := count_mismatched_pairs(arr);
}
// </vc-code>
