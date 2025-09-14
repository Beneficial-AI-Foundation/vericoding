function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma count_append_one(s: seq<int>, x: int)
  ensures count_negative_temp_days(s + [x]) == count_negative_temp_days(s) + (if x < 0 then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert count_negative_temp_days(s) == 0;
    assert count_negative_temp_days(s + [x]) == (if (s + [x])[0] < 0 then 1 else 0) + count_negative_temp_days((s + [x])[1..]);
    assert (s + [x])[0] == x;
    assert (s + [x])[1..] == [];
    assert count_negative_temp_days([]) == 0;
    assert count_negative_temp_days(s + [x]) == (if x < 0 then 1 else 0) + 0;
    assert count_negative_temp_days(s + [x]) == count_negative_temp_days(s) + (if x < 0 then 1 else 0);
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];

    assert count_negative_temp_days(s + [x]) ==
      (if (s + [x])[0] < 0 then 1 else 0) + count_negative_temp_days((s + [x])[1..]);
    assert count_negative_temp_days(s + [x]) ==
      (if s[0] < 0 then 1 else 0) + count_negative_temp_days(s[1..] + [x]);

    count_append_one(s[1..], x);

    assert count_negative_temp_days(s[1..] + [x]) ==
      count_negative_temp_days(s[1..]) + (if x < 0 then 1 else 0);

    assert count_negative_temp_days(s + [x]) ==
      (if s[0] < 0 then 1 else 0) + (count_negative_temp_days(s[1..]) + (if x < 0 then 1 else 0));

    assert count_negative_temp_days(s) ==
      (if s[0] < 0 then 1 else 0) + count_negative_temp_days(s[1..]);

    assert ((if s[0] < 0 then 1 else 0) + (count_negative_temp_days(s[1..]) + (if x < 0 then 1 else 0)))
         == (((if s[0] < 0 then 1 else 0) + count_negative_temp_days(s[1..])) + (if x < 0 then 1 else 0));

    assert count_negative_temp_days(s + [x]) ==
      count_negative_temp_days(s) + (if x < 0 then 1 else 0);
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
  var c := count_negative_temp_days(temps);
  if c > k {
    result := -1;
  } else {
    var i := 0;
    var found := false;
    var idx := -1;
    while i < n
      invariant 0 <= i <= n
      invariant !found ==> forall j :: 0 <= j < i ==> temps[j] >= 0
      invariant found ==> 0 <= idx && idx < i && temps[idx] < 0
    {
      if !found && temps[i] < 0 {
        found := true;
        idx := i;
      }
      i := i + 1;
    }
    if found {
      result := 1;
    } else {
      result := 0;
    }
  }
}
// </vc-code>

