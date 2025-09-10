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
lemma DivDecrease(n: nat, d: nat)
  requires n > 0 && d > 1 && n % d == 0 && n >= d
  ensures n / d < n
{
  var q := n / d;
  // From n % d == 0 we have n == q * d
  assert q * d == n;
  // q cannot be 0 because that would imply n == 0, contradicting n > 0
  if q == 0 {
    assert n == 0;
    assert false;
  }
  assert q >= 1;
  // d >= 2 because d > 1
  assert d >= 2;
  // n == q * d and d >= 2 imply n >= 2 * q
  assert n == q * d;
  assert n >= 2 * q;
  // From q >= 1 and n >= 2*q we get n > q
  assert q < n;
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
  result := count_valid_k_values(n);
  if n == 1 {
    assert result == -1;
  } else {
    assert result == count_divisors(n - 1) + count_special_divisors(n) - 1;
  }
  assert result >= -1;
}
// </vc-code>

