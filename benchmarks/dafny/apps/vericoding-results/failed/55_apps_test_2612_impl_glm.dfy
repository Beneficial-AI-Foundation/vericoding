predicate is_valid_beautiful_arrangement(arrangement: seq<int>, sizes: seq<int>)
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
{
    |arrangement| >= 1 &&
    // All indices are distinct
    (forall i, j :: 0 <= i < j < |arrangement| ==> arrangement[i] != arrangement[j]) &&
    // Indices are in increasing order
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    // Adjacent elements satisfy divisibility constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    // Adjacent elements satisfy size constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

predicate ValidInput(n: int, sizes: seq<int>)
{
    n >= 1 && |sizes| == n && forall i :: 0 <= i < n ==> sizes[i] >= 1
}

// <vc-helpers>
lemma DivisibilityTransitive(a: int, b: int, c: int)
    requires a != 0 && b != 0 && c != 0
    requires b % a == 0 && c % b == 0
    ensures c % a == 0
{
    assert b == a * (b / a);
    assert c == b * (c / b);
    assert c == a * (b / a) * (c / b);
    assert c % a == 0;
}

lemma BeautifulArrangementExtension(arrangement: seq<int>, sizes: seq<int>, new_elem: int)
    requires is_valid_beautiful_arrangement(arrangement, sizes)
    requires 1 <= new_elem <= |sizes|
    requires forall i :: 0 <= i < |arrangement| ==> arrangement[i] != new_elem
    requires |arrangement| > 0 ==> new_elem % arrangement[|arrangement| - 1] == 0
    requires |arrangement| > 0 ==> sizes[arrangement[|arrangement| - 1] - 1] < sizes[new_elem - 1]
    ensures is_valid_beautiful_arrangement(arrangement + [new_elem], sizes)
{
    var new_arr := arrangement + [new_elem];
    assert |new_arr| >= 1;
    
    // All indices are distinct
    assert forall i, j :: 0 <= i < j < |new_arr| ==> new_arr[i] != new_arr[j]
    by {
        forall i, j | 0 <= i < j < |new_arr|
        ensures new_arr[i] != new_arr[j]
        {
            if j < |arrangement| {
                assert new_arr[i] == arrangement[i];
                assert new_arr[j] == arrangement[j];
                assert arrangement[i] != arrangement[j] by { assert is_valid_beautiful_arrangement(arrangement, sizes); }
            } else if i < |arrangement| {
                assert new_arr[i] == arrangement[i];
                assert new_arr[j] == new_elem;
                assert arrangement[i] != new_elem by { assert forall i :: 0 <= i < |arrangement| ==> arrangement[i] != new_elem; }
            } else {
                // This case can't happen since i < j
            }
        }
    }
    
    // Indices are in increasing order
    assert forall i :: 0 <= i < |new_arr| - 1 ==> new_arr[i] < new_arr[i + 1]
    by {
        forall i | 0 <= i < |new_arr| - 1
        ensures new_arr[i] < new_arr[i + 1]
        {
            if i < |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == arrangement[i + 1];
                assert arrangement[i] < arrangement[i + 1] by { assert is_valid_beautiful_arrangement(arrangement, sizes); }
            } else if i == |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == new_elem;
                assert arrangement[i] < new_elem by {
                    if arrangement[i] < new_elem {
                    } else if arrangement[i] == new_elem {
                        assert false by { assert forall i :: 0 <= i < |arrangement| ==> arrangement[i] != new_elem; }
                    }
                }
            }
        }
    }
    
    // Adjacent elements satisfy divisibility constraint
    assert forall i :: 0 <= i < |new_arr| - 1 ==> new_arr[i + 1] % new_arr[i] == 0
    by {
        forall i | 0 <= i < |new_arr| - 1
        ensures new_arr[i + 1] % new_arr[i] == 0
        {
            if i < |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == arrangement[i + 1];
                assert arrangement[i + 1] % arrangement[i] == 0 by { assert is_valid_beautiful_arrangement(arrangement, sizes); }
            } else if i == |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == new_elem;
                assert new_elem % arrangement[i] == 0 by { assert |arrangement| > 0 ==> new_elem % arrangement[|arrangement| - 1] == 0; }
            }
        }
    }
    
    // Adjacent elements satisfy size constraint
    assert forall i :: 0 <= i < |new_arr| - 1 ==> sizes[new_arr[i] - 1] < sizes[new_arr[i + 1] - 1]
    by {
        forall i | 0 <= i < |new_arr| - 1
        ensures sizes[new_arr[i] - 1] < sizes[new_arr[i + 1] - 1]
        {
            if i < |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == arrangement[i + 1];
                assert sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1] by { assert is_valid_beautiful_arrangement(arrangement, sizes); }
            } else if i == |arrangement| - 1 {
                assert new_arr[i] == arrangement[i];
                assert new_arr[i + 1] == new_elem;
                assert sizes[arrangement[i] - 1] < sizes[new_elem - 1] by { assert |arrangement| > 0 ==> sizes[arrangement[|arrangement| - 1] - 1] < sizes[new_elem - 1]; }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sizes: seq<int>) returns (result: int)
    requires ValidInput(n, sizes)
    ensures 1 <= result <= n
    ensures forall arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) ==> |arrangement| <= result
    ensures exists arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) && |arrangement| == result
// </vc-spec>
// <vc-code>
{
  var dp := new int[n];
  for i := 0 to n-1 {
      dp[i] := 1;
  }

  for i := 0 to n-1 {
      for j := 0 to i-1 {
          if (i+1) % (j+1) == 0 && sizes[j] < sizes[i] {
              if dp[j] + 1 > dp[i] {
                  dp[i] := dp[j] + 1;
              }
          }
      }
  }

  var max := 1;
  for i := 0 to n-1 {
      if dp[i] > max {
          max := dp[i];
      }
  }
  result := max;
}
// </vc-code>

