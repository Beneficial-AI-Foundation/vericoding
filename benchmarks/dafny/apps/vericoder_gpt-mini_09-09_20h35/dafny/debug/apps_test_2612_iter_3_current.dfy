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
// Added no helpers; invariants in the implementation suffice for verification.
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
  var dp := new int[n + 1];
  var prev := new int[n + 1];

  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant forall t :: 1 <= t < j ==>
      (forall arr :: (forall k :: 0 <= k < |arr| ==> 1 <= arr[k] <= n) && is_valid_beautiful_arrangement(arr, sizes) && arr[|arr|-1] == t ==> |arr| <= dp[t]) &&
      (exists arr :: (forall k :: 0 <= k < |arr| ==> 1 <= arr[k] <= n) && is_valid_beautiful_arrangement(arr, sizes) && arr[|arr|-1] == t && |arr| == dp[t]) &&
      (prev[t] == 0 ==> dp[t] == 1) &&
      (prev[t] != 0 ==> 1 <= prev[t] < t && t % prev[t] == 0 && sizes[prev[t] - 1] < sizes[t - 1] && dp[t] == dp[prev[t]] + 1)
  {
    dp[j] := 1;
    prev[j] := 0;

    var i := 1;
    while i < j
      invariant 1 <= i <= j
      invariant forall t :: 1 <= t < j ==>
        (forall arr :: (forall k :: 0 <= k < |arr| ==> 1 <= arr[k] <= n) && is_valid_beautiful_arrangement(arr, sizes) && arr[|arr|-1] == t ==> |arr| <= dp[t]) &&
        (exists arr :: (forall k :: 0 <= k < |arr| ==> 1 <= arr[k] <= n) && is_valid_beautiful_arrangement(arr, sizes) && arr[|arr|-1] == t && |arr| == dp[t]) &&
        (prev[t] == 0 ==> dp[t] == 1) &&
        (prev[t] != 0 ==> 1 <= prev[t] < t && t % prev[t] == 0 && sizes[prev[t] - 1] < sizes[t - 1] && dp[t] == dp[prev[t]] + 1)
      invariant prev[j] == 0 || (1 <= prev[j] < j && j % prev[j] == 0 && sizes[prev[j] - 1] < sizes[j - 1] && dp[j] == dp[prev[j]] + 1)
    {
      if j % i == 0 && sizes[i - 1] < sizes[j - 1] && dp[i] + 1 > dp[j] {
        dp[j] := dp[i] + 1;
        prev[j] := i;
      }
      i := i + 1;
    }

    // Prove maximality: any valid arrangement ending at j has length <= dp[j]
    assert forall arr ::
      (forall k :: 0 <= k < |arr| ==> 1 <= arr[k] <= n) && is_valid_beautiful_arrangement(arr, sizes) && arr[|arr|-1] == j ==>
      |arr| <= dp[j]
    by {
      // Let arr be such an arrangement.
      var arr0 := arr;
      if |arr0| == 1 {
        // length 1 <= dp[j] because dp[j] >= 1
        assert dp[j] >= 1;
      } else {
        var pred := arr0[|arr0| - 2];
        var prefix := arr0[..|arr0| - 1];
        // prefix is a valid arrangement ending at pred, and pred < j
        assert prefix[|prefix| - 1] == pred;
        // By outer invariant (since pred < j), prefix length <= dp[pred]
        assert |prefix| <= dp[pred];
        // adjacency gives divisibility and sizes constraints between pred and j
        assert j % pred == 0;
        assert sizes[pred - 1] < sizes[j - 1];
        // dp[j] was computed considering dp[pred] + 1, so dp[j] >= dp[pred] + 1
        assert dp[j] >= dp[pred] + 1;
        assert |arr0| == |prefix| + 1 <= dp[pred] + 1 <= dp[j];
      }
    }

    // Prove existence: there exists a valid arrangement ending at j with length dp[j]
    if prev[j] == 0 {
      // dp[j] == 1, witness is [j]
      assert dp[j] == 1;
      assert exists witness :: witness == [j] && (forall k :: 0 <= k < |witness| ==> 1 <= witness[k] <= n) && is_valid_beautiful_arrangement(witness, sizes) && |witness| == dp[j];
    } else {
      var p := prev[j];
      // p is a valid predecessor: p < j and divisibility and size constraints hold, and dp[j] == dp[p] + 1
      assert 1 <= p < j;
      assert j % p == 0;
      assert sizes[p - 1] < sizes[j - 1];
      assert dp[j] == dp[p] + 1;

      // By outer invariant there exists an arrangement ending at p of length dp[p]
      var arr_p : seq<int> :| (forall k :: 0 <= k < |arr_p| ==> 1 <= arr_p[k] <= n) && is_valid_beautiful_arrangement(arr_p, sizes) && arr_p[|arr_p|-1] == p && |arr_p| == dp[p];
      var arr_j := arr_p + [j];
      // arr_j is valid: arr_p ends at p < j, and j%p==0, sizes[p-1] < sizes[j-1] hold
      assert is_valid_beautiful_arrangement(arr_j, sizes);
      assert arr_j[|arr_j|-1] == j;
      assert |arr_j| == dp[p] + 1;
      assert dp[j] == dp[p] + 1;
      assert |arr_j| == dp[j];
    }

    j := j + 1;
  }

  // Find index with maximal dp value
  var idx := 1;
  var k := 2;
  while k <= n
    invariant 2 <= k <= n + 1
    invariant 1 <= idx <= n
    invariant forall t :: 1 <= t < k ==> dp[t] <= dp[idx]
  {
    if dp[k] > dp[idx] {
      idx := k;
    }
    k := k + 1;
  }

  // idx has maximal dp; set result and provide witness arrangement
  result := dp[idx];
  assert 1 <= result <= n;

  // By outer invariant (after processing all j) there exists an arrangement ending at idx with length dp[idx]
  var finalArr : seq<int> :| (forall k0 :: 0 <= k0 < |finalArr| ==> 1 <= finalArr[k0] <= n) && is_valid_beautiful_arrangement(finalArr, sizes) && finalArr[|finalArr|-1] == idx && |finalArr| == dp[idx];
  // This establishes the existence postcondition.
}
// </vc-code>

