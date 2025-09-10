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
function reduce_by_divisor_iter(n: nat, d: nat): nat
  requires n > 0 && d > 1
  decreases if n % d == 0 && n >= d then n / d else n
{
  if n % d == 0 && n >= d then
    reduce_by_divisor_iter(n / d, d)
  else n
}

lemma lemma_reduce_by_divisor_iter_eq_reduce_by_divisor(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor_iter(n, d) == reduce_by_divisor(n, d)
{
  if n % d == 0 && n >= d then
    lemma_reduce_by_divisor_iter_eq_reduce_by_divisor(n / d, d);
  // This is a direct consequence of the functions being identical.
  // No explicit proof steps needed beyond the compiler's understanding of function equality.
}

lemma lemma_count_divisors_spec(n: nat)
  requires n > 0
  ensures count_divisors(n) == |set d | 1 <= d <= n && n % d == 0|
{
  // This is a direct consequence of the function definition.
}

lemma lemma_count_special_divisors_spec(n: nat)
  requires n > 0
  ensures count_special_divisors(n) == |set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|
{
  // This is a direct consequence of the function definition.
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
    var num_divisors_n_minus_1 := count_divisors(n - 1);
    var num_special_divisors_n := count_special_divisors(n);
    if num_divisors_n_minus_1 + num_special_divisors_n == 0 && n > 1 {
      return -1; 
    } else {
      return num_divisors_n_minus_1 + num_special_divisors_n - 1;
    }
  }
}
// </vc-code>

