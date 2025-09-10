predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma sum_arithmetic_series(k: int) returns (s: int)
  requires k >= 0
  ensures s == k * (k + 1) / 2
{
  s := 0;
  var i := 0;
  while i <= k
    invariant 0 <= i <= k + 1
    invariant s == i * (i - 1) / 2
  {
    s := s + i;
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
  if !IsPossible(n, k)
  {
    return [-1];
  }

  var s: seq<int> := new int[k];
  var currentSum := 0;
  for i := 0 to k - 1
    invariant 0 <= i <= k
    invariant |s| == k
    invariant forall j :: 0 <= j < i ==> s[j] > 0
    invariant forall j :: 0 <= j < i - 1 ==> s[j] < s[j+1]
    invariant currentSum == sum(s[..i])
    invariant forall j :: i <= j < k ==> s[j] == 0 // elements after i are not yet set
  {
    s[i] := i + 1;
    currentSum := currentSum + (i + 1);
  }

  assert currentSum == k * (k + 1) / 2 by {
    sum_arithmetic_series(k);
    assert sum(s) == k * (k + 1) / 2; // sum(s) here is just currentSum as sum is over the whole seq s
  }

  var remaining = n - currentSum;
  assert remaining >= 0; // Because of IsPossible check

  var base_add = remaining / k;
  var remainder_add = remaining % k;

  for i := 0 to k - 1
    invariant 0 <= i <= k
    invariant |s| == k
    invariant (sum(s) + (k - i) * base_add + (k - i) * (if i <= remainder_add then 1 else 0)) == n // n is invariant
    invariant forall j :: 0 <= j < i ==> s[j] == old(s)[j] + base_add + (if j < remainder_add then 1 else 0)
    invariant forall j :: i <= j < k ==> s[j] == old(s)[j] + base_add // Not quite, elements after i are yet to be incremented
    invariant forall x :: 0 <= x < i ==> s[x] > 0
    invariant forall x :: 0 <= x < i - 1 ==> s[x] < s[x+1]
  {
    s[i] := s[i] + base_add;
    if i >= k - remainder_add
    {
      s[i] := s[i] + 1;
    }
  }

  // Ensure result sequence properties
  result := s;

  // Proof that result satisfies IsStrictlyIncreasing
  forall i | 0 <= i < k - 1
    ensures result[i] < result[i+1]
  {
    var val_i = (i + 1) + base_add + (if i >= k - remainder_add then 1 else 0);
    var val_i_plus_1 = ((i + 1) + 1) + base_add + (if (i + 1) >= k - remainder_add then 1 else 0);

    if i+1 < k - remainder_add {
      // Both i and i+1 are not in the remainder_add group
      assert val_i == (i + 1) + base_add;
      assert val_i_plus_1 == (i + 2) + base_add;
      assert val_i < val_i_plus_1;
    } else if i >= k - remainder_add {
      // Both i and i+1 are in the remainder_add group
      assert val_i == (i + 1) + base_add + 1;
      assert val_i_plus_1 == (i + 2) + base_add + 1;
      assert val_i < val_i_plus_1;
    } else { // i < k - remainder_add and i+1 >= k - remainder_add
      // i is not in remainder_add group, i+1 is in remainder_add group
      assert val_i == (i + 1) + base_add;
      assert val_i_plus_1 == (i + 2) + base_add + 1;
      assert val_i < val_i_plus_1;
    }
  }

  // Proof that result satisfies AllPositive
  forall i | 0 <= i < k
    ensures result[i] > 0
  {
    assert result[i] == (i + 1) + base_add + (if i >= k - remainder_add then 1 else 0);
    assert (i + 1) >= 1;
    assert base_add >= 0;
    assert result[i] >= 1;
  }

  // Proof that sum(result) == n
  var finalSum := 0;
  for i := 0 to k - 1
    invariant 0 <= i <= k
    invariant finalSum == sum(result[..i])
  {
    finalSum := finalSum + result[i];
  }
  assert finalSum == n;

  return result;
}
// </vc-code>

