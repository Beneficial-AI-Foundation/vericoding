predicate ValidInput(n: int, m: int)
{
  n >= m > 0
}

function sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function count(s: seq<int>, val: int): int
{
  if |s| == 0 then 0 
  else (if s[0] == val then 1 else 0) + count(s[1..], val)
}

predicate OptimalDistribution(result: seq<int>, n: int, m: int)
  requires m > 0
{
  |result| == m &&
  (forall i :: 0 <= i < |result| ==> result[i] > 0) &&
  sum(result) == n &&
  (forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1) &&
  count(result, n / m) == m - (n % m) &&
  count(result, n / m + 1) == n % m
}

// <vc-helpers>
lemma lemma_sum_prefix(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s[0..i]) == (if i == 0 then 0 else s[0] + sum(s[1..i]))
{
  if i == 0 {
    // sum(s[0..0]) is sum(empty sequence) which is 0
  } else {
    // sum(s[0..i]) is s[0] + sum(s[1..i]) by definition of sum
  }
}

lemma lemma_sum_array_prefix(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  ensures sum(a[0..i]) == Helpers.ArraySum(a, i) // Use a ghost function for the sum
{
  // The lemma itself doesn't need to return anything; its purpose is to prove the `ensures` clause.
  // The ghost function `Helpers.ArraySum` can be used in specifications.
}

// Introduce a ghost module to hold ghost functions for specifications
module Helpers {
  ghost function ArraySum(a: array<int>, i: int): int
    requires 0 <= i <= a.Length
  {
    if i == 0 then 0 else a[i-1] + ArraySum(a, i-1)
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: seq<int>)
  requires ValidInput(n, m)
  ensures OptimalDistribution(result, n, m)
// </vc-spec>
// <vc-code>
{
    var q := n / m;
    var r := n % m;
    var result_arr := new int[m];

    var i := 0;
    var current_sum := 0; // Keep track of sum for invariant
    while i < m
      invariant 0 <= i <= m
      invariant result_arr.Length == m
      invariant forall k :: 0 <= k < i ==> result_arr[k] == q || result_arr[k] == q + 1
      invariant forall k :: 0 <= k < i ==> result_arr[k] > 0
      invariant (forall k :: 0 <= k < i && k < r ==> result_arr[k] == q + 1)
      invariant (forall k :: r <= k < i ==> result_arr[k] == q)
      invariant current_sum == Helpers.ArraySum(result_arr, i) // Use ghost function here
      invariant current_sum == i * q + (if i <= r then i else r)
    {
        if i < r {
            result_arr[i] := q + 1;
            current_sum := current_sum + q + 1;
        } else {
            result_arr[i] := q;
            current_sum := current_sum + q;
        }
        i := i + 1;
    }

    result := result_arr[..];

    assert |result| == m;
    assert forall k :: 0 <= k < |result| ==> result[k] > 0;

    // Use the `current_sum` from the loop to prove `sum(result) == n`
    lemma_sum_array_prefix(result_arr, m); // Call the lemma to establish its ensures clause
    assert Helpers.ArraySum(result_arr, m) == current_sum; // Use ghost function for assertion
    assert sum(result_arr[0..m]) == current_sum; // This is now provable from lemma_sum_array_prefix

    assert current_sum == r * (q + 1) + (m - r) * q;
    assert r * (q + 1) + (m - r) * q == r * q + r + m * q - r * q;
    assert r * q + r + m * q - r * q == r + m * q;
    assert r + m * q == n % m + (n/m) * m;
    assert n % m + (n/m) * m == n;
    assert current_sum == n;
    assert sum(result) == current_sum;
    assert sum(result) == n;


    assert (forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1);

    var count_q := 0;
    var count_q_plus_1 := 0;
    var k := 0;
    while k < m
      invariant 0 <= k <= m
      invariant count_q == count(result_arr[0..k], q)
      invariant count_q_plus_1 == count(result_arr[0..k], q + 1)
      invariant (forall ki :: 0 <= ki < k && ki < r ==> result_arr[ki] == q + 1)
      invariant (forall ki :: r <= ki < k ==> result_arr[ki] == q)
      // The following invariants directly relate count_q and count_q_plus_1 to k and r
      // These are crucial for proving the final counts.
      invariant count_q == (if k <= r then 0 else k - r)
      invariant count_q_plus_1 == (if k <= r then k else r)
    {
        if k < r {
            assert result_arr[k] == q + 1;
            count_q_plus_1 := count_q_plus_1 + 1;
        } else {
            assert result_arr[k] == q;
            count_q := count_q + 1;
        }
        k := k + 1;
    }
    assert count(result, n / m) == m - (n % m);
    assert count(result, n / m + 1) == n % m;
}
// </vc-code>

