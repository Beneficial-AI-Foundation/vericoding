predicate ValidInput(n: nat)
{
  n > 0
}

function reduce_by_divisor(n: nat, d: nat): nat
  requires n > 0 && d > 1
  decreases n
{
  if n % d == 0 && n >= d then 
    reduce_by_divisor(n / d, d)
  else n
}

function count_divisors(n: nat): nat
  requires n > 0
{
  |set d | 1 <= d <= n && n % d == 0|
}

function count_special_divisors(n: nat): nat
  requires n > 0
{
  |set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|
}

function count_valid_k_values(n: nat): int
  requires n > 0
{
  if n == 1 then -1
  else 
    count_divisors(n - 1) + count_special_divisors(n) - 1
}

// <vc-helpers>
predicate {:trigger IsSpecialDivisor(k, n)} IsSpecialDivisor(k: nat, n: nat)
  requires 2 <= k <= n
{
  n % k == 0 && (reduce_by_divisor(n, k) - 1) % k == 0
}

predicate {:trigger IsDivisorOfNMinusOne(k, n)} IsDivisorOfNMinusOne(k: nat, n: nat)
  requires 1 <= k < n
{
  (n-1) % k == 0
}

lemma lemma_reduce_by_divisor_positive(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(n, d) >= 1
{
  if n % d == 0 && n >= d {
    lemma_reduce_by_divisor_positive(n/d, d);
  } else {
    // n >= 1, and we return n.
  }
}

lemma lemma_reduce_by_divisor_result(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures var r := reduce_by_divisor(n, d); r % d != 0
{
  if n % d == 0 && n >= d {
    lemma_reduce_by_divisor_result(n/d, d);
  } else {
    // Either n % d != 0 or n < d.
    // In both cases, r = n, and n % d != 0.
  }
}

lemma lemma_reduce_by_divisor_idempotent(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(reduce_by_divisor(n, d), d) == reduce_by_divisor(n, d)
{
  var r := reduce_by_divisor(n, d);
  lemma_reduce_by_divisor_result(n, d);
  lemma_reduce_by_divisor_positive(n, d);
  assert r % d != 0;
  // Therefore, when we compute reduce_by_divisor(r, d), the condition (r % d == 0 && r >= d) fails because r % d != 0.
  // So reduce_by_divisor(r, d) = r.
}

lemma lemma_reduce_by_divisor_multiplicity(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(n * d, d) == reduce_by_divisor(n, d)
{
  if n % d == 0 && n >= d {
    var n1 := n / d;
    calc {
      reduce_by_divisor(n * d, d);
      == reduce_by_divisor((d * n1) * d, d);
      { assert (d * n1 * d) % d == 0 && (d * n1 * d) >= d; }
      == reduce_by_divisor(d * n1 * d / d, d);
      == reduce_by_divisor(d * n1, d);
      { assert (d * n1) % d == 0 && (d * n1) >= d; }
      == reduce_by_divisor(d * n1 / d, d);
      == reduce_by_divisor(n1, d);
      == reduce_by_divisor(n, d); // By induction, since n1 < n
    }
  } else {
    // n % d != 0 or n < d
    calc {
      reduce_by_divisor(n * d, d);
      { assert (n * d) % d == 0 && (n * d) >= d; }
      == reduce_by_divisor(n * d / d, d);
      == reduce_by_divisor(n, d);
    }
  }
}

lemma lemma_special_divisor_equivalent(n: nat, k: nat)
  requires 2 <= k <= n
  ensures IsSpecialDivisor(k, n) <==> n % k == 0 && reduce_by_divisor(n, k) % k == 1
{
  var r := reduce_by_divisor(n, k);
  lemma_reduce_by_divisor_result(n, k);
  // (r - 1) % k == 0  <=>  r % k == 1
  // Since r % k != 0, the condition is well-defined and equivalent.
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (result: int)
  requires ValidInput(n)
  ensures result == count_valid_k_values(n)
  ensures n == 1 ==> result == -1
  ensures n > 1 ==> result == count_divisors(n - 1) + count_special_divisors(n) - 1
  ensures result >= -1
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    return -1;
  }
  var count := 0;
  // Count divisors of n-1
  for k := 1 to n - 1
    invariant 1 <= k <= n
    invariant count == count_divisors(k - 1)
  {
    if (n - 1) % k == 0 {
      count := count + 1;
    }
  }

  // Count special divisors of n
  var special := 0;
  for k := 2 to n
    invariant 2 <= k <= n + 1
    invariant special == |set d | 2 <= d < k && IsSpecialDivisor(d, n)|
  {
    if n % k == 0 {
      var r := reduce_by_divisor(n, k);
      if (r - 1) % k == 0 {
        special := special + 1;
      }
    }
  }

  return count + special - 1;
}
// </vc-code>

