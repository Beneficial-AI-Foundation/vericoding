type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountOccurrences<T>(s: seq<T>, x: T) returns (count: nat)
  ensures count == |set j | 0 <= j < |s| && s[j] == x|
{
  count := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant count == |set j | 0 <= j < i && s[j] == x|
  {
    if s[i] == x {
      count := count + 1;
    }
  }
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

  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant forall k :: k in counts ==> counts[k] == CountOccurrences(a[0..i], k)
    invariant max_count == (max(map_values(counts)) whenever counts != map[])
    invariant max_count == 0 ==> counts == map[]
    // If counts is not empty, max_val is one of the keys that has max_count
    invariant counts != map[] ==> max_val in counts && counts[max_val] == max_count
    // If counts is not empty, then max_val is one of the keys for the maximum count
    invariant counts != map[] ==> forall k :: k in counts ==> counts[k] <= max_count
  {
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
    }
    // If current_count == max_count and current_val is already the max_val
    // or if `max_count` was 0, it means `counts` was empty and `max_count` just became 1.
    // In this case, `max_val` becomes `current_val`.
    else if max_count == 0 {
      max_val := current_val;
      max_count := current_count;
    }
  }

  biggest := map[];
  if max_count > 0 { // max_count will be 0 only if a is empty
    biggest := map[max_val := max_count];
  }

  // Prove first post-condition
  forall i_idx | 0 <= i_idx < |a| && a[i_idx] in biggest ensures biggest[a[i_idx]] == |set j | 0 <= j < |a| && a[j] == a[i_idx]|
  {
    var key := a[i_idx];
    assert key in biggest; // This means key == max_val
    assert biggest[key] == max_count;
    assert max_count == CountOccurrences(a, max_val);
    assert max_count == CountOccurrences(a, key);
  }

  // Prove second post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest ensures biggest[a[i_idx]] >= |set k | 0 <= k < |a| && a[k] == a[j_idx]|
  {
    if a[i_idx] in biggest {
      var key_i := a[i_idx];
      var val_i := biggest[key_i];
      // val_i must be max_count
      assert val_i == max_count;
      // We need to show max_count >= CountOccurrences(a, a[j_idx])
      // This holds by definition of max_count being the maximum count of any element in `a`.
      assert max_count >= CountOccurrences(a, a[j_idx]);
    }
  }

  // Prove third post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest && a[j_idx] in biggest ensures biggest[a[i_idx]] == biggest[a[j_idx]]
  {
    if a[i_idx] in biggest && a[j_idx] in biggest {
      // If a[i_idx] is in biggest, it must be the key 'max_val'
      assert a[i_idx] == max_val;
      // Similarly, if a[j_idx] is in biggest, it must also be the key 'max_val'
      assert a[j_idx] == max_val;
      // Therefore, their counts must be the same (max_count)
      assert biggest[a[i_idx]] == max_count;
      assert biggest[a[j_idx]] == max_count;
    }
  }
}
// </vc-code>

