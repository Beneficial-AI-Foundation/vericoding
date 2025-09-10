function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma count_negative_bound(temps: seq<int>)
  ensures count_negative_temp_days(temps) >= 0
  ensures count_negative_temp_days(temps) <= |temps|
{
  if |temps| == 0 {
  } else {
    count_negative_bound(temps[1..]);
  }
}

lemma slice_index_correspondence(temps: seq<int>)
  requires |temps| > 0
  ensures forall i :: 1 <= i < |temps| ==> temps[i] == temps[1..][i-1]
{
  if |temps| <= 1 {
    return;
  }
  
  assert |temps[1..]| == |temps| - 1;
  
  forall i | 1 <= i < |temps|
    ensures temps[i] == temps[1..][i-1]
  {
    assert 0 <= i-1 < |temps[1..]|;
  }
}

lemma count_negative_zero_iff_all_non_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 <==> forall i :: 0 <= i < |temps| ==> temps[i] >= 0
{
  if |temps| == 0 {
  } else {
    count_negative_zero_iff_all_non_negative(temps[1..]);
    slice_index_correspondence(temps);
    
    if count_negative_temp_days(temps) == 0 {
      assert temps[0] >= 0;
      assert count_negative_temp_days(temps[1..]) == 0;
      assert forall i :: 0 <= i < |temps[1..]| ==> temps[1..][i] >= 0;
      assert forall i :: 0 <= i < |temps| ==> temps[i] >= 0;
    }
    if forall i :: 0 <= i < |temps| ==> temps[i] >= 0 {
      assert temps[0] >= 0;
      assert forall i :: 0 <= i < |temps[1..]| ==> temps[1..][i] >= 0;
      assert count_negative_temp_days(temps[1..]) == 0;
      assert count_negative_temp_days(temps) == 0;
    }
  }
}

lemma count_negative_positive_iff_exists_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 <==> exists i :: 0 <= i < |temps| && temps[i] < 0
{
  if |temps| == 0 {
  } else {
    count_negative_positive_iff_exists_negative(temps[1..]);
    assert (exists i :: 1 <= i < |temps| && temps[i] < 0) <==> (exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0);
    if count_negative_temp_days(temps) > 0 {
      if temps[0] < 0 {
        assert exists i :: 0 <= i < |temps| && temps[i] < 0;
      } else {
        assert count_negative_temp_days(temps[1..]) > 0;
        assert exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0;
        assert exists i :: 0 <= i < |temps| && temps[i] < 0;
      }
    }
    if exists i :: 0 <= i < |temps| && temps[i] < 0 {
      if temps[0] < 0 {
        assert count_negative_temp_days(temps) > 0;
      } else {
        assert exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0;
        assert count_negative_temp_days(temps[1..]) > 0;
        assert count_negative_temp_days(temps) > 0;
      }
    }
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
  count_negative_bound(temps);
  var negative_count := count_negative_temp_days(temps);
  
  if negative_count > k {
    result := -1;
  } else {
    result := negative_count;
    count_negative_zero_iff_all_non_negative(temps);
    if result > 0 {
      count_negative_positive_iff_exists_negative(temps);
      assert result == count_negative_temp_days(temps);
      assert count_negative_temp_days(temps) > 0;
    }
  }
}
// </vc-code>

