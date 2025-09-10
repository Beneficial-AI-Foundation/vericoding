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
lemma reduce_by_divisor_property(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(n, d) > 0
  ensures var r := reduce_by_divisor(n, d); r % d != 0 || r < d
  decreases n
{
  if n % d == 0 && n >= d {
    assert n / d < n;
    reduce_by_divisor_property(n / d, d);
  }
}

lemma count_divisors_non_zero(n: nat)
  requires n > 0
  ensures count_divisors(n) > 0
{
  assert 1 >= 1;
  assert 1 <= n;
  assert n % 1 == 0;
  assert 1 in set d | 1 <= d <= n && n % d == 0;
  assert |set d | 1 <= d <= n && n % d == 0| >= 1;
}

lemma count_special_divisors_non_negative(n: nat)
  requires n > 0
  ensures count_special_divisors(n) >= 0
{
  forall d {:trigger reduce_by_divisor(n, d)} | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0
  ensures d >= 2
  {
  }
}

lemma count_valid_k_values_properties(n: nat)
  requires n > 0
  ensures count_valid_k_values(n) >= -1
{
  if n == 1 {
    calc {
      count_valid_k_values(1);
      -1;
    }
  } else {
    calc {
      count_valid_k_values(n);
      count_divisors(n - 1) + count_special_divisors(n) - 1;
      >= { count_divisors_non_zero(n - 1); } 1 + 0 - 1;
      > -1;
    }
  }
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
  } else {
    return count_divisors(n - 1) + count_special_divisors(n) - 1;
  }
}
// </vc-code>

