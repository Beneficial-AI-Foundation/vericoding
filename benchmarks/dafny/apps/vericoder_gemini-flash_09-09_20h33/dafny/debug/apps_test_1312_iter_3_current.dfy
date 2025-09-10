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

lemma lemma_sum_array_prefix(a: array<int>, i: int) returns (s: int)
  requires 0 <= i <= a.Length
  ensENSURES s == sum(a[0..i])
{
  var current_sum := 0;
  var k := 0;
  while k < i
    invariant 0 <= k <= i
    invariant current_sum == sum(a[0..k])
  {
    current_sum := current_sum + a[k];
    k := k + 1;
  }
  return current_sum;
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
      invariant current_sum == sum(result_arr[0..i])
      invariant current_sum == i * q + (if i <= r then i else r)
    {
        if i < r {
            result_arr[i] := q + 1;
            current_sum := current_sum + (q + 1);
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
      invariant count_q == k - (if k <= r then k else r)
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

