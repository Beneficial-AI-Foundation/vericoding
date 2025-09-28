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
lemma CountUpToStep(arr: seq<int>, i: int)
  requires 0 <= i < |arr| / 2
  ensures count_mismatched_pairs_up_to(arr, i+1) == count_mismatched_pairs_up_to(arr, i) + (if arr[i] != arr[|arr| - 1 - i] then 1 else 0)
{
  // Unfold the definition for count_mismatched_pairs_up_to at i+1
  assert count_mismatched_pairs_up_to(arr, i+1) ==
    (if (i+1) == 0 then 0 else (if arr[(i+1)-1] != arr[|arr| - (i+1)] then 1 else 0) + count_mismatched_pairs_up_to(arr, (i+1)-1));
  assert (i+1)-1 == i;
  assert |arr| - (i+1) == |arr| - 1 - i;
  assert (if arr[i] != arr[|arr| -1 - i] then 1 else 0) + count_mismatched_pairs_up_to(arr, i) ==
         count_mismatched_pairs_up_to(arr, i) + (if arr[i] != arr[|arr| -1 - i] then 1 else 0);
  assert count_mismatched_pairs_up_to(arr, i+1) == count_mismatched_pairs_up_to(arr, i) + (if arr[i] != arr[|arr| -1 - i] then 1 else 0);
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
  var n := |arr|;
  var lim := n / 2;
  var i := 0;
  changes := 0;
  while i < lim
    invariant 0 <= i <= lim
    invariant 0 <= changes <= i
    invariant changes == count_mismatched_pairs_up_to(arr, i)
  {
    if arr[i] != arr[n - 1 - i] {
      changes := changes + 1;
    }
    i := i + 1;
  }
  assert changes == count_mismatched_pairs_up_to(arr, lim);
  assert changes == count_mismatched_pairs(arr);
}

// </vc-code>
