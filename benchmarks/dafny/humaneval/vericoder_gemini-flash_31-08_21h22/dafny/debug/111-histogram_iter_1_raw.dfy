```vc-helpers
lemma CountOccurrences<T>(s: seq<T>, x: T) returns (count: int)
  ensures count == |set j | 0 <= j < |s| && s[j] == x|
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |set j | 0 <= j < i && s[j] == x|
  {
    if s[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
}
```

```vc-code
{
  biggest := map[];
  if |a| == 0 {
    return biggest;
  }

  var first_val_count := -1;
  var processed_elements := {};

  for i := 0 to |a|-1
    invariant 0 <= i <= |a|
    invariant processed_elements == set j | 0 <= j < i :: a[j]
    invariant forall k :: 0 <= k < i && a[k] in biggest ==> biggest[a[k]] == first_val_count
    invariant first_val_count == -1 || (forall k :: 0 <= k < i && a[k] in processed_elements && a[k] == a[0] ==> CountOccurrences(a, a[k]) == first_val_count)
    invariant forall k :: 0 <= k < i && a[k] in biggest && biggest[a[k]] > 0
  {
    var current_val := a[i];
    if current_val !in processed_elements {
      processed_elements := processed_elements + {current_val};
      var current_val_count := CountOccurrences(a, current_val);

      if first_val_count == -1 {
        first_val_count := current_val_count;
        biggest := biggest + {current_val := current_val_count};
      } else if current_val_count == first_val_count {
        biggest := biggest + {current_val := current_val_count};
      } else {
        // If counts are different, no element satisfies the condition, so biggest remains empty or is cleared.
        // In the context of the postconditions requiring ALL elements to have the same count,
        // if even one pair has different counts, no such map exists satisfying the postconditions.
        // However, the postcondition implies that if `a[i] in biggest`, then its count must match.
        // It does not say that `biggest` must contain *all* elements, only those that satisfy the conditions.
        // If, for example, `first_val_count` was 2, and `current_val_count` is 3, then `biggest` can't contain both.
        // If it means "find the most frequent values *which all have the same frequency*", then we need to handle this.
        // The postcondition `biggest[a[i]] == biggest[a[j]]` for all `a[i], a[j]` in biggest is key.
        // This implies that if we add any element to `biggest`, we *must* maintain this property.
        // Thus, if current_val_count != first_val_count, this 'biggest' map cannot satisfy the property,
        // and per the spec, if there is ANY element in 'a' whose count is different from 'first_val_count',
        // 'biggest' map must be 'map[]' effectively, unless all elements in 'a' have the same count.
        // The simplest approach that always satisfies the property is to only add elements that match the first encountered count.
        // If a mismatch occurs, we can stop building BiggestMap with elements, or keep it empty, ensuring correctness.
        // Let's assume the intent is to collect elements that *all* have the most frequent count, and all elements in `biggest` have that same most frequent count.
        // The postcondition `biggest[a[i]] == biggest[a[j]]` is the most restrictive one.
        // If we found a `current_val` whose count is different from `first_val_count`,
        // then either `first_val_count` wasn't the actual "biggest" count for ALL elements that will be in the map,
        // or we need to discard all elements and make `biggest` empty OR ensure `first_val_count` is the actual count of all elements in the final `biggest` map.
        // Given the phrasing: "biggest[a[i]] == biggest[a[j]]", it means ALL elements in `biggest` MUST have the SAME count.
        // If `first_val_count != current_val_count`, then we know that not all distinct elements have the same count.
        // Therefore, it's impossible to create a `biggest` map containing any elements that satisfies the postconditions,
        // unless all elements in 'a' themselves have the same count.
        // The strongest postcondition is `biggest[a[i]] == biggest[a[j]]`. If we add 'x' with count Cx and 'y' with count Cy, and Cx != Cy, this postcondition is violated.
        // The solution is to ensure `biggest` only contains elements that share a consistent frequency IF that frequency is >= other frequencies.
        // The last postcondition: `biggest[a[i]] == biggest[a[j]]` means all values in the output map must have the exact same count.
        // The second postcondition: `biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|` means that common count must be greater or equal to any other element's count.
        // This is a tricky interpretation. Let's assume for simplicity, it implies that *if* there is a common, globally maximal frequency, that's what we collect.
        // If there are multiple frequencies among elements of `a`, it's impossible to satisfy `biggest[a[i]] >= |set k | ... |` and `biggest[a[i]] == biggest[a[j]]` simultaneously,
        // unless `biggest` contains only elements that have *the* most common frequency, and all elements that HAVE that frequency are included.
        // If we find `current_val_count` is different from `first_val_count`, it means there's no single value `C` such that all elements in `a` occur `C` times.
        // Thus, the only map `biggest` that can satisfy `biggest[a[i]] == biggest[a[j]]` for all i,j is `map[]`.
        // The spec implies a specific scenario for `biggest` not being empty.
        // If all distinct elements in `a` occur with the *same* frequency, then `biggest` will be populated.
        // If they don't, `biggest` must remain empty to satisfy the `biggest[a[i]] == biggest[a[j]]` property.

        // So, if we find current_val_count != first_val_count, and first_val_count was already set,
        // it means we've found elements with different counts. This violates the implicit requirement
        // that all elements mapped in `biggest` have the same count AND that common count is maximal.
        // Therefore, the only way to satisfy the postconditions is for `biggest` to be empty.
        biggest := map[]; // Clear biggest, as consistent count for all relevant elements is broken.
        break; // No need to continue if inconsistency found.
      }
    }
  }

  // After the loop, if biggest is not empty, all elements in it have `first_val_count`.
  // We need to ensure this `first_val_count` is indeed greater or equal to any other count.
  // This is typically true by construction IF `biggest` is not cleared because of a count mismatch.
  // The first ensures: `biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|` means exactly:
  // if `a[i]` is in `biggest`, its associated value must be its true count. This is what we stored.
  // The third ensures: `biggest[a[i]] == biggest[a[j]]` means all values in `biggest` are the same.
  // This is maintained by `first_val_count` logic.

  // The problematic one is `biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|`.
  // This means the count value stored in `biggest` (which is `first_val_count`) must be
  // greater than or equal to the count of ANY element `a[j]` in the original sequence `a`.
  // This implies that `first_val_count` must be the *maximum* count of any element in `a`.
  // If this is the case, then if `biggest` is not empty, `first_val_count` must be the global maximum count.
  // This means if we encounter ANY element `current_val` whose count is greater than `first_val_count`,
  // then our `first_val_count` was not the maximal count. In this case, `biggest` should be empty.
  // Effectively, the map `biggest` will contain `e -> C` for certain `e` if and only if
  // C is the _unique_ maximal frequency among all elements in `a`, and all elements `e` that appear `C` times.
  // If there are multiple maximal frequencies, or if not all elements with the maximal frequency are picked (not expressible directly),
  // OR if there are elements with different frequencies, the only map `biggest` that satisfies all Post Conditions is `map[]`.

  // Let's re-evaluate the logic based on the toughest postcondition:
  // `ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==> biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|`
  // This means if `a[i]` is in `biggest`, then `biggest[a[i]]` (which is its count) must be `>=` any other element's count in `a`.
  // This directly means `biggestValue` (the single count for all elements in `biggest`) must be the maximum frequency in `a`.
  // And `ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==> biggest[a[i]] == biggest[a[j]]`
  // This means if `a[i]` and `a[j]` are in `biggest`, they must have the same count.

  // Combined, this implies:
  // 1. Find the maximum frequency, `M`, among all elements in `a`.
  // 2. If there are multiple elements that have this maximum frequency `M`, then `biggest` should map all such elements to `M`.
  //    And this `M` must be the only value.
  //    If there are elements that *also* have this same `M` frequency but are not included, it contradicts the first ensures
  //    `biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|` because this ensures that if `a[i]` is in `biggest`, `biggest[a[i]]` must be its count.
  // The first `ensures` basically implies that `biggest` only contains counts for items that are actually in `a`.

  // The initial strategy: accumulate counts for distinct elements, and if `first_val_count` is established, and a new element's count `current_val_count` is different:
  //   - If `current_val_count > first_val_count`: The `first_val_count` was not maximal. So it's impossible to satisfy second postcondition. `biggest` must be empty.
  //   - If `current_val_count < first_val_count`: Similar to above, if `first_val_count` is the global max, this is fine.
  //   - If `current_val_count != first_val_count` AND `first_val_count` was the *initial* candidate for the common biggest count,
  //     then it means not all elements (that eventually constitute `biggest`) have the same count.
  //     So, `biggest` must be empty.

  // Let's refine the logic:
  // 1. Calculate all counts.
  var counts: map<int, int> := map[];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: k in counts && 0 <= k < i ==> counts[a[k]] == CountOccurrences(a[0..i], a[k])
    invariant forall k :: k in counts ==> counts[k] > 0
  {
    var current_val := a[i];
    counts := counts[current_val := (if current_val in counts then counts[current_val] else 0) + 1];
    i := i + 1;
  }

  // 2. Find the maximum frequency.
  var max_freq := 0;
  if |a| > 0 {
    // If counts is empty but |a| > 0, this means a contains only duplicates of same value.
    // E.g., a = [1, 1, 1], counts = {1:3}.
    // This part assumes 'counts' will have entries if |a| > 0.
    // If a non-empty sequence `a` results in an empty `counts` map, then `max_freq` should correctly be 0.
    // This happens only if `a` is empty, or if an empty `counts` map is possible for non-empty `a`, which it's not.
    // `counts` will contain entries for all unique elements in `a`.
    for key, value in counts {
      if value > max_freq {
        max_freq := value;
      }
    }
  }

  // 3. Populate `biggest` based on computed maximum frequency and the "all in biggest have same count" rule.
  biggest := map[];
  if max_freq == 0 { // Handles empty sequence 'a'
    return biggest;
  }

  var all_items_have_same_max_freq := true;
  for key, value in counts {
    if value != max_freq {
      all_items_have_same_max_freq := false;
      break;
    }
  }

  if all_items_have_same_max_freq {
    for key, value in counts {
      biggest := biggest + {key := value};
    }
  } else {
    // There are elements with counts different from max_freq.
    // The postcondition `biggest[a[i]] == biggest[a[j]]` requires all values in `biggest` to have the same count.
    // The postcondition `biggest[a[i]] >= |set k | ... |` requires this count to be >= any element's count.
    // If we only add elements with `max_freq` to `biggest`, the third postcondition holds.
    // The second postcondition `biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|` will be satisfied,
    // because `max_freq` is indeed the maximum.
    // The first postcondition `biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|` will also be satisfied.
    // So, we just filter elements that have `max_freq`.

    for key, value in counts {
      if value == max_freq {
        biggest := biggest + {key := value};
      }
    }
  }

  return biggest;
}
```