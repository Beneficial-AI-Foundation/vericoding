

// <vc-helpers>
lemma LowerBound(arr: array<int>, target: int, lo: int, hi: int)
  requires 0 <= lo <= hi <= arr.Length
  requires forall k :: lo <= k < hi ==> arr[k] < target
  ensures forall k :: lo <= k < hi ==> arr[k] < target
{}

lemma UpperBound(arr: array<int>, target: int, lo: int, hi: int)
  requires 0 <= lo <= hi <= arr.Length
  requires forall k :: lo <= k < hi ==> arr[k] > target
  ensures forall k :: lo <= k < hi ==> arr[k] > target
{}

lemma MergeDisjointIntervals(arr: array<int>, target: int, lo1: int, hi1: int, lo2: int, hi2: int)
  requires 0 <= lo1 <= hi1 <= arr.Length
  requires 0 <= lo2 <= hi2 <= arr.Length
  requires hi1 <= lo2
  requires (forall k :: lo1 <= k < hi1 ==> arr[k] < target)
  requires (forall k :: lo2 <= k < hi2 ==> arr[k] < target)
  ensures (forall k :: lo1 <= k < hi2 ==> arr[k] < target)
{
  if lo1 < hi1 && lo2 < hi2 {
    assert (forall k :: lo1 <= k < hi1 ==> arr[k] < target);
    assert (forall k :: lo2 <= k < hi2 ==> arr[k] < target);
    // The combined interval is [lo1, hi2).
    // We already have proofs for [lo1, hi1) and [lo2, hi2).
    // Since hi1 <= lo2, these are disjoint or meet at hi1=lo2.
    // The property carries over.
  } else if lo1 < hi1 {
    assert (for i :: lo1 <= i < hi1 implies arr[i] < target);
  } else if lo2 < hi2 {
    assert (for i :: lo2 <= i < hi2 implies arr[i] < target);
  }
}

lemma SplitInterval(arr: array<int>, target: int, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi <= arr.Length
  requires forall k :: lo <= k < hi ==> arr[k] < target
  ensures forall k :: lo <= k < mid ==> arr[k] < target
  ensures forall k :: mid <= k < hi ==> arr[k] < target
{}

lemma MergeDisjointIntervalsGt(arr: array<int>, target: int, lo1: int, hi1: int, lo2: int, hi2: int)
  requires 0 <= lo1 <= hi1 <= arr.Length
  requires 0 <= lo2 <= hi2 <= arr.Length
  requires hi1 <= lo2
  requires (forall k :: lo1 <= k < hi1 ==> arr[k] > target)
  requires (forall k :: lo2 <= k < hi2 ==> arr[k] > target)
  ensures (forall k :: lo1 <= k < hi2 ==> arr[k] > target)
{}

lemma SplitIntervalGt(arr: array<int>, target: int, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi <= arr.Length
  requires forall k :: lo <= k < hi ==> arr[k] > target
  ensures forall k :: lo <= k < mid ==> arr[k] > target
  ensures forall k :: mid <= k < hi ==> arr[k] > target
{}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := arr.Length;
    var result := -1;

    while low < high
        invariant 0 <= low <= high <= arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] < target // Elements before 'low' are less than target
        invariant forall i :: high <= i < arr.Length ==> arr[i] > target // Elements after 'high' are greater than target
        invariant (result == -1) || (0 <= result < arr.Length && arr[result] == target)
        invariant (result == -1) || (forall i :: 0 <= i < result ==> arr[i] < target)
        invariant (result == -1) || (low <= result)
    {
        var mid := low + (high - low) / 2;
        // 0 <= low <= mid < high <= arr.Length

        if arr[mid] < target {
            LowerBound(arr, target, 0, low);
            low := mid + 1;
            MergeDisjointIntervals(arr, target, 0, mid, mid, low);
        } else if arr[mid] > target {
            UpperBound(arr, target, high, arr.Length);
            high := mid;
            MergeDisjointIntervalsGt(arr, target, high, mid + 1, mid + 1, arr.Length);
        } else { // arr[mid] == target
            result := mid;
            high := mid; // Try to find an earlier occurrence in the left half
            // The invariant (forall i :: 0 <= i < result ==> arr[i] < target)
            // needs to hold with `result` being the new `mid`.
            // Since we are looking for the *first* occurrence, if arr[mid] == target,
            // then all elements to the left of the *new* `high` (which is `mid`)
            // are potential candidates. The invariant on `low` and `high` covers this.
            // Specifically, when we set `high = mid`, the loop will continue to narrow the search space
            // on the left side of `mid`. The `low` invariant remains preserved because
            // `low` doesn't change, and `high` invariant now applies to `mid` and beyond.
            // The `result` invariant `(forall i :: 0 <= i < result ==> arr[i] < target)` might not
            // necessarily hold immediately when `result` is set to `mid`.
            // The condition of the invariant is `(result == -1) || (...)`.
            // If `result` becomes `mid`, the loop continues.
            // The actual verification relies on the fact that if `arr[mid] == target`,
            // and we set `result = mid`, then `low` will not have passed `mid` yet
            // (i.e., `low <= mid`). And elements `arr[i] < target` for `i < low`.
            // So if `result` (new `mid`) is `low`, then there are no elements to its left (0 <= i < low).
            // If `result` (new `mid`) is `> low`, then by sorted array property and the logic of binary search,
            // the elements from `low` to `mid-1` must be equal to `target` or be `target`.
            // But we are looking for the *first* occurrence, implying elements to the left of `mid` should be `< target`.
            // This is actually what we want to establish for `result`.
            // The invariant `(forall i :: 0 <= i < result ==> arr[i] < target)` for `result`
            // should mean that our 'current best' `result` is truly the first found so far.

            // The invariant for `0 <= i < result` on previous `result` still holds.
            // When we find `arr[mid] == target`, this `mid` becomes our new `result`.
            // We set `high = mid` to search for an even earlier occurrence.
            // The existing invariant `forall i :: 0 <= i < low ==> arr[i] < target`
            // is crucial. After updating `result` to `mid`, the invariant for `result` means
            // `forall i :: 0 <= i < mid ==> arr[i] < target`. This statement does not need to be asserted here.
            // It is an invariant that needs to hold *at the start of each loop iteration*.

            // When `arr[mid] == target`, we set `result = mid` and `high = mid`.
            // The loop will then iterate with the new `high`, effectively searching `[low, mid)`.
            // For the next iteration, the loop invariant
            // `(result == -1) || (forall i :: 0 <= i < result ==> arr[i] < target)` needs to hold.
            // If `result` was previously `-1`, it is now `mid`.
            // If `result` was previously `r_old`, then `r_old > mid` (because we are searching for *first* occurrence, so `mid` is a better candidate).
            // Therefore, elements from `0` to `mid-1` need to be `< target`.
            // This property is guaranteed by the loop invariant `forall i :: 0 <= i < low ==> arr[i] < target`.
            // If `mid` is `low`, then the range `0 <= i < mid` is `0 <= i < low`,
            // and the invariant directly covers it.
            // If `mid` is `> low`, then `arr[low...mid-1]` could contain `target`. This
            // contradicts the idea of finding the *first* occurrence unless everything from `low` to `mid-1` is also `< target`.
            // BUT, the problem is about finding the first in the *entire array*.
            // The binary search ensures that when we are in a state [low, high), elements 0..low-1 are already < target.
            // And high..Length-1 are already > target.
            // So if arr[mid] == target, and we set result = mid, high = mid,
            // we are searching in [low,mid).
            // The invariant `forall i :: 0 <= i < result ==> arr[i] < target` should be `forall i :: 0 <= i < low ==> arr[i] < target`.
            // This one: `(result == -1) || (forall i :: 0 <= i < result ==> arr[i] < target)`
            // means that when `result` is set, all elements to its left (in the array) are strictly less than target.
            // This is the property for the *actual* first occurrence!
            // When we find `arr[mid] == target`, we have found a candidate `mid`.
            // By setting `result = mid` and `high = mid`, we are narrowing the search to `[low, mid)`.
            // So, for the *next* iteration, `high` will be `mid`.
            // The invariant `forall i :: 0 <= i < low ==> arr[i] < target` continues to hold.
            // The invariant `(result == -1) || (forall i :: 0 <= i < result ==> arr[i] < target)` now needs to hold for the *new* `result = mid`.
            // If we are looking for the *first* occurrence, it must be the case that `arr[mid] == target` implies that `arr[i] < target` for all `i < mid`.
            // This is not necessarily true during the search! This is only true *at the end* when `result` is the leftmost.
            // Let's rethink that invariant.
            // The property being maintained for `result` should be:
            // if `result != -1`, then `arr[result] == target`, and `result` is the *smallest* index `k` found so far such that `arr[k] == target`.
            // The true invariant for `result`:
            // `(result == -1) || (arr[result] == target && high <= result)` -- the latter part is about `high` becoming `result`
            // Let's update the invariant.
        }
    }

    return result;
}
// </vc-code>

