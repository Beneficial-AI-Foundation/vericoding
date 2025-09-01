type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountOccurrences<T>(s: seq<T>, x: T) returns (count: nat)
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

function max_of_set(s: set<int>): int
  requires s != {}
  ensures max_of_set(s) in s
  ensures forall x :: x in s ==> x <= max_of_set(s)
{
  var current_max: int := s.Any(); // Initialize with an arbitrary element from the set
  for x in s
    invariant current_max in s
    invariant forall y :: y in s && y <= x ==> y <= current_max // Elements processed up to x are less than or equal current_max
    invariant forall y :: y in s && y <= x && y > current_max ==> false // No element processed so far is greater than current_max
  {
    if x > current_max {
      current_max := x;
    }
  }
  return current_max;
}

function map_values<K, V>(m: map<K, V>): set<V> {
  set v | exists k :: k in m && m[k] == v
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var counts: map<int, int> := map[];
  var max_count := 0;
  var max_val := 0; // arbitrary initial value, will be updated

  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall k :: k in counts ==> counts[k] == CountOccurrences(a[0..i], k)
    invariant (counts != map[]) ==> max_count == max_of_set(map_values(counts))
    invariant (counts == map[]) ==> max_count == 0
    invariant (counts != map[]) ==> (exists k :: k in counts && counts[k] == max_count)
    invariant (counts != map[]) ==> max_val in counts && counts[max_val] == max_count
    invariant (counts != map[]) ==> forall k :: k in counts ==> counts[k] <= max_count
  {
    if i < |a| {
      var current_val := a[i];
      var current_count := 0;
      if current_val in counts {
        current_count := counts[current_val] + 1;
      } else {
        current_count := 1;
      }
      counts := counts[current_val := current_count];

      if current_count > max_count {
        max_count := current_count;
        max_val := current_val;
      } else if max_count == 0 || (current_count == max_count && max_val == 0 && current_val != 0) { // This case handles the first element being processed
        // If max_count is 0, it means 'counts' was empty or all values were 0.
        // This implies this is the first element added with a positive count.
        // Or if the map contained zeros, and this is the first non-zero count.
        // It's crucial to set max_val here.
        max_val := current_val;
        max_count := current_count;
      }
    }
  }

  biggest := map[];
  if max_count > 0 {
    biggest := map[max_val := max_count];
  }

  // Prove first post-condition
  forall i_idx | 0 <= i_idx < |a| && a[i_idx] in biggest ensures biggest[a[i_idx]] == CountOccurrences(a, a[i_idx])
  {
    var key := a[i_idx];
    assert biggest[key] == max_count;
    // The invariant `counts[k] == CountOccurrences(a[0..i], k)` applies for 'i' up to |a|.
    // So for i = |a|, we have `counts[k] == CountOccurrences(a, k)`.
    // And from invariant `counts != map[] ==> max_val in counts && counts[max_val] == max_count`
    // And if max_count > 0, then counts != map[], so `counts[max_val] == max_count`.
    // Combining these: `max_count == CountOccurrences(a, max_val)`.
    assert max_count == CountOccurrences(a, max_val);
    assert max_val == key; // Since key is in biggest, it must be max_val
  }

  // Prove second post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest ensures biggest[a[i_idx]] >= CountOccurrences(a, a[j_idx])
  {
    if a[i_idx] in biggest {
      var key_i := a[i_idx];
      var val_i := biggest[key_i];
      assert val_i == max_count; // From definition of biggest map
      assert max_count == CountOccurrences(a, max_val); // As shown for post-condition 1
      assert max_val == a[i_idx]; // Because a[i_idx] is the key in biggest, it must be max_val

      // From invariant: forall k :: k in counts ==> counts[k] <= max_count
      // When the loop finishes, 'counts' contains the final counts for all elements in 'a'.
      // So, CountOccurrences(a, k) == counts[k] for k in counts.
      // We need to establish that CountOccurrences(a, a[j_idx]) is one of these counts.
      // If a[j_idx] appeared in 'a', then a[j_idx] is a key in 'counts' (or it's 0 if not present).
      if a[j_idx] in counts {
          assert counts[a[j_idx]] == CountOccurrences(a, a[j_idx]);
          assert counts[a[j_idx]] <= max_count; // By loop invariant
      } else {
          // If a[j_idx] is not in counts, it means its count is 0.
          assert CountOccurrences(a, a[j_idx]) == 0;
          assert 0 <= max_count; // Max count is always non-negative
      }
    }
  }

  // Prove third post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest && a[j_idx] in biggest ensures biggest[a[i_idx]] == biggest[a[j_idx]]
  {
    if a[i_idx] in biggest && a[j_idx] in biggest {
      // By definition of 'biggest' map, if a[i_idx] is in biggest, it must be 'max_val'.
      assert a[i_idx] == max_val;
      // Similarly for a[j_idx].
      assert a[j_idx] == max_val;
      // Therefore, both keys are the same, and their values in 'biggest' must be 'max_count'.
      assert biggest[a[i_idx]] == max_count;
      assert biggest[a[j_idx]] == max_count;
    }
  }
}
// </vc-code>

