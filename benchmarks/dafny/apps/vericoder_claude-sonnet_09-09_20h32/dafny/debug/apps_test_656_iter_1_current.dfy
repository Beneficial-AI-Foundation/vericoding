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

lemma count_negative_zero_iff_all_non_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 <==> forall i :: 0 <= i < |temps| ==> temps[i] >= 0
{
  if |temps| == 0 {
  } else {
    count_negative_zero_iff_all_non_negative(temps[1..]);
  }
}

lemma count_negative_positive_iff_exists_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 <==> exists i :: 0 <= i < |temps| && temps[i] < 0
{
  if |temps| == 0 {
  } else {
    count_negative_positive_iff_exists_negative(temps[1..]);
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
    count_negative_positive_iff_exists_negative(temps);
  }
}
// </vc-code>

