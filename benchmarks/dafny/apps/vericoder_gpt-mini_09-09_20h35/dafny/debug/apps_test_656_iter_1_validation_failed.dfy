function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma CountNonNeg(temps: seq<int>)
  ensures count_negative_temp_days(temps) >= 0
  decreases |temps|
{
  if |temps| == 0 {
    // count = 0
  } else {
    var rest := temps[1..];
    CountNonNeg(rest);
    var r := count_negative_temp_days(rest);
    assert count_negative_temp_days(temps) == (if temps[0] < 0 then 1 else 0) + r;
    if temps[0] < 0 {
      assert (if temps[0] < 0 then 1 else 0) + r >= 0;
    } else {
      assert r >= 0;
      assert (if temps[0] < 0 then 1 else 0) + r >= 0;
    }
  }
}

lemma CountZeroImplAllNonNeg(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 ==> forall i :: 0 <= i < |temps| ==> temps[i] >= 0
  decreases |temps|
{
  if |temps| == 0 {
    // vacuously true
  } else {
    var rest := temps[1..];
    if count_negative_temp_days(temps) == 0 {
      var r := count_negative_temp_days(rest);
      assert (if temps[0] < 0 then 1 else 0) + r == 0;
      if temps[0] < 0 {
        // impossible
        assert false;
      }
      // temps[0] >= 0
      CountZeroImplAllNonNeg(rest);
      assert forall i :: 0 <= i < |rest| ==> rest[i] >= 0;
      // prove for all i in temps
      assert forall i :: 0 <= i < |temps| ==>
        (if i == 0 then temps[0] >= 0 else rest[i-1] >= 0) by {
          var i:int;
          assume 0 <= i < |temps|;
          if i == 0 {
            assert temps[0] >= 0;
          } else {
            assert 0 <= i-1 < |rest|;
            assert rest[i-1] >= 0;
          }
        }
      // the above implies the desired property
      assert forall i :: 0 <= i < |temps| ==> temps[i] >= 0;
    }
  }
}

lemma CountPosImplExistsNeg(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 ==> exists i :: 0 <= i < |temps| && temps[i] < 0
  decreases |temps|
{
  if |temps| == 0 {
    // impossible to have count > 0
  } else {
    var rest := temps[1..];
    if count_negative_temp_days(temps) > 0 {
      var r := count_negative_temp_days(rest);
      if temps[0] < 0 {
        exists 0;
        assert 0 <= 0 < |temps| && temps[0] < 0;
      } else {
        // temps[0] >= 0, so count = r and r > 0
        assert count_negative_temp_days(temps) == 0 + r;
        assert r > 0;
        CountPosImplExistsNeg(rest);
        // pick a witness from the proven existence on rest
        var j :| 0 <= j < |rest| && rest[j] < 0;
        exists j + 1;
        assert 0 <= j + 1 < |temps|;
        assert temps[j + 1] < 0;
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
  var cnt := count_negative_temp_days(temps);
  // instantiate helpful lemmas for the verifier
  CountNonNeg(temps);
  CountZeroImplAllNonNeg(temps);
  CountPosImplExistsNeg(temps);

  if cnt > k {
    result := -1;
    return;
  } else {
    result := cnt;
    return;
  }
}
// </vc-code>

