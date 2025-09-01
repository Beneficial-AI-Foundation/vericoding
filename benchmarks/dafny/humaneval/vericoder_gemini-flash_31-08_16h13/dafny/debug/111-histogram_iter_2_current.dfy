type BiggestMap = map<int, int>

// <vc-helpers>
lemma CountOccurrences<T>(s: seq<T>, x: T) returns (count: nat)
  ensures count == |set j | 0 <= j < |s| && s[j] == x|
{
  count := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant count == |set j | 0 <= j < i && s[j] == x|
  {
    if i < |s| && s[i] == x { // Added i < |s| check
      count := count + 1;
    }
  }
}

function max(s: set<int>): int
  requires s != {}
{
  var res := 0;
  if s != {}
  {
    res := arbitrary;
    for x in s
      invariant x in s
      invariant res in s
      invariant forall y | y in s && y <= x :: y <= res
    {
      if x > res {
        res := x;
      }
    }
  }
  res
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
    invariant counts != map[] ==> max_count == max(map_values(counts))
    invariant counts == map[] ==> max_count == 0
    invariant counts != map[] ==> max_val in counts && counts[max_val] == max_count
    invariant counts != map[] ==> forall k :: k in counts ==> counts[k] <= max_count
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
      } else if max_count == 0 { // This case handles the first element being processed
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
    assert key == max_val; // Since key is in biggest, it must be max_val
    assert biggest[key] == max_count;
    assert max_count == CountOccurrences(a, max_val); // This comes from the loop invariant
    assert CountOccurrences(a, max_val) == CountOccurrences(a, key);
  }

  // Prove second post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest ensures biggest[a[i_idx]] >= CountOccurrences(a, a[j_idx])
  {
    if a[i_idx] in biggest {
      var key_i := a[i_idx];
      var val_i := biggest[key_i];
      assert val_i == max_count;
      assert max_count == CountOccurrences(a, max_val);
      assert (forall k :: k in a[0..|a|] ==> CountOccurrences(a, k) <= max_count); // By loop invariant
      assert CountOccurrences(a, a[j_idx]) <= max_count;
    }
  }

  // Prove third post-condition
  forall i_idx, j_idx | 0 <= i_idx < |a| && 0 <= j_idx < |a| && a[i_idx] in biggest && a[j_idx] in biggest ensures biggest[a[i_idx]] == biggest[a[j_idx]]
  {
    if a[i_idx] in biggest && a[j_idx] in biggest {
      assert a[i_idx] == max_val;
      assert a[j_idx] == max_val;
      assert biggest[a[i_idx]] == max_count;
      assert biggest[a[j_idx]] == max_count;
    }
  }
}
// </vc-code>

