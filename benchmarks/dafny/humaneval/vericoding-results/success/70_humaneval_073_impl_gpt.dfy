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
lemma lemma_count_up_to_bounds(arr: seq<int>, limit: int)
  requires 0 <= limit <= |arr| / 2
  ensures 0 <= count_mismatched_pairs_up_to(arr, limit)
  ensures count_mismatched_pairs_up_to(arr, limit) <= limit
  decreases limit
{
  if limit == 0 {
  } else {
    assert limit > 0;
    assert 0 <= limit - 1 <= |arr| / 2;
    lemma_count_up_to_bounds(arr, limit - 1);
    assert count_mismatched_pairs_up_to(arr, limit) ==
      (if arr[limit - 1] != arr[|arr| - limit] then 1 else 0) +
      count_mismatched_pairs_up_to(arr, limit - 1);
    assert 0 <= (if arr[limit - 1] != arr[|arr| - limit] then 1 else 0) <= 1;
    assert count_mismatched_pairs_up_to(arr, limit) >= count_mismatched_pairs_up_to(arr, limit - 1);
    assert count_mismatched_pairs_up_to(arr, limit) <= count_mismatched_pairs_up_to(arr, limit - 1) + 1;
    assert 0 <= count_mismatched_pairs_up_to(arr, limit);
    assert count_mismatched_pairs_up_to(arr, limit) <= limit;
  }
}

lemma lemma_count_bounds(arr: seq<int>)
  ensures 0 <= count_mismatched_pairs(arr)
  ensures count_mismatched_pairs(arr) <= |arr| / 2
{
  lemma_count_up_to_bounds(arr, |arr| / 2);
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
  lemma_count_bounds(arr);
  changes := count_mismatched_pairs(arr);
}
// </vc-code>
