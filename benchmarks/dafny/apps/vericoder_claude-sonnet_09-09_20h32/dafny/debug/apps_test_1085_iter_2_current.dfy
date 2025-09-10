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
lemma count_divisors_positive(n: nat)
  requires n > 0
  ensures count_divisors(n) >= 1
{
  assert 1 in set d | 1 <= d <= n && n % d == 0;
}

lemma count_special_divisors_non_negative(n: nat)
  requires n > 0
  ensures count_special_divisors(n) >= 0
{
}

lemma result_bound(n: nat)
  requires n > 1
  ensures count_divisors(n - 1) + count_special_divisors(n) - 1 >= 0
{
  count_divisors_positive(n - 1);
  count_special_divisors_non_negative(n);
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
  count_divisors_positive(n);
  if n == 1 {
    result := -1;
  } else {
    result_bound(n);
    result := count_divisors(n - 1) + count_special_divisors(n) - 1;
  }
}
// </vc-code>

