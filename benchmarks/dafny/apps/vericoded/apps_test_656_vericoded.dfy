function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma count_negative_temp_days_bounds(temps: seq<int>)
  ensures 0 <= count_negative_temp_days(temps) <= |temps|
{
  if |temps| == 0 {
    // Base case: empty sequence
  } else {
    // Inductive case
    count_negative_temp_days_bounds(temps[1..]);
  }
}

lemma count_negative_zero_iff_all_nonnegative(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 <==> (forall i :: 0 <= i < |temps| ==> temps[i] >= 0)
{
  if |temps| == 0 {
    // Base case: empty sequence
  } else {
    // Inductive case
    count_negative_zero_iff_all_nonnegative(temps[1..]);
    
    if count_negative_temp_days(temps) == 0 {
      // If count is 0, then temps[0] >= 0 and count for rest is 0
      // By definition: count_negative_temp_days(temps) = (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
      // Since count_negative_temp_days(temps) == 0, and count_negative_temp_days(temps[1..]) >= 0
      // We must have (if temps[0] < 0 then 1 else 0) == 0
      // Therefore temps[0] >= 0
      assert count_negative_temp_days(temps) == (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..]);
      count_negative_temp_days_bounds(temps[1..]);
      assert count_negative_temp_days(temps[1..]) >= 0;
      assert (if temps[0] < 0 then 1 else 0) == 0;
      assert temps[0] >= 0;
      assert count_negative_temp_days(temps[1..]) == 0;
      assert forall i :: 0 <= i < |temps[1..]| ==> temps[1..][i] >= 0;
      assert forall i :: 0 <= i < |temps| ==> temps[i] >= 0;
    }
    
    if forall i :: 0 <= i < |temps| ==> temps[i] >= 0 {
      // If all are non-negative, count is 0
      assert temps[0] >= 0;
      assert forall i :: 0 <= i < |temps[1..]| ==> temps[1..][i] >= 0;
      assert count_negative_temp_days(temps[1..]) == 0;
      assert count_negative_temp_days(temps) == 0;
    }
  }
}

lemma count_negative_positive_exists_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 <==> (exists i :: 0 <= i < |temps| && temps[i] < 0)
{
  if |temps| == 0 {
    // Base case: empty sequence
    assert count_negative_temp_days(temps) == 0;
  } else {
    // Inductive case
    count_negative_positive_exists_negative(temps[1..]);
    
    if count_negative_temp_days(temps) > 0 {
      // If count > 0, then either temps[0] < 0 or count for rest > 0
      if temps[0] < 0 {
        assert exists i :: 0 <= i < |temps| && temps[i] < 0;
      } else {
        assert count_negative_temp_days(temps[1..]) > 0;
        assert exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0;
        var j :| 0 <= j < |temps[1..]| && temps[1..][j] < 0;
        assert temps[j+1] < 0;
        assert exists i :: 0 <= i < |temps| && temps[i] < 0;
      }
    }
    
    if exists i :: 0 <= i < |temps| && temps[i] < 0 {
      // If negative exists, count > 0
      var j :| 0 <= j < |temps| && temps[j] < 0;
      if j == 0 {
        assert temps[0] < 0;
        // By definition: count_negative_temp_days(temps) = (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
        // Since temps[0] < 0, we have: count_negative_temp_days(temps) = 1 + count_negative_temp_days(temps[1..])
        assert count_negative_temp_days(temps) == (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..]);
        assert (if temps[0] < 0 then 1 else 0) == 1;
        count_negative_temp_days_bounds(temps[1..]);
        assert count_negative_temp_days(temps[1..]) >= 0;
        assert count_negative_temp_days(temps) == 1 + count_negative_temp_days(temps[1..]);
        assert count_negative_temp_days(temps) >= 1;
      } else {
        assert temps[j] == temps[1..][j-1];
        assert exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0;
        assert count_negative_temp_days(temps[1..]) > 0;
        assert count_negative_temp_days(temps) == (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..]);
        assert count_negative_temp_days(temps) > 0;
      }
    }
  }
}

lemma count_negative_append(temps: seq<int>, x: int)
  ensures count_negative_temp_days(temps + [x]) == count_negative_temp_days(temps) + (if x < 0 then 1 else 0)
{
  if |temps| == 0 {
    assert temps + [x] == [x];
    assert count_negative_temp_days([x]) == (if x < 0 then 1 else 0);
  } else {
    assert (temps + [x])[0] == temps[0];
    assert (temps + [x])[1..] == temps[1..] + [x];
    count_negative_append(temps[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, temps: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 0 && k <= n
  requires |temps| == n
  requires forall i :: 0 <= i < n ==> -20 <= temps[i] <= 20
  ensures result == -1 <==> count_negative_temp_days(temps) > k
  ensures result != -1 ==> result >= 0
  ensures result == 0 ==> forall i :: 0 <= i < n ==> temps[i] >= 0
  ensures result > 0 ==> exists i :: 0 <= i < n && temps[i] < 0
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant count == count_negative_temp_days(temps[..i])
  {
    if temps[i] < 0 {
      count := count + 1;
    }
    assert temps[..i+1] == temps[..i] + [temps[i]];
    count_negative_append(temps[..i], temps[i]);
    i := i + 1;
  }
  
  assert temps[..n] == temps;
  assert count == count_negative_temp_days(temps);
  
  if count > k {
    result := -1;
  } else {
    result := count;
    count_negative_zero_iff_all_nonnegative(temps);
    count_negative_positive_exists_negative(temps);
  }
}
// </vc-code>

