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
method reduce_by_divisor_iter(n: nat, d: nat) returns (res: nat)
    requires n > 0 && d > 1
    ensures res == reduce_by_divisor(n, d)
    ensures res > 0
{
    var current_n := n;
    while current_n % d == 0 && current_n >= d
        decreases current_n
        invariant current_n > 0
        invariant reduce_by_divisor(n, d) == reduce_by_divisor(current_n, d)
    {
        current_n := current_n / d;
    }
    res := current_n;
    assert reduce_by_divisor(res, d) == res;
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
    result := -1;
    return;
  }
  
  // n > 1
  var n_minus_1 := n - 1;

  var count1: nat := 0;
  var d1: nat := 1;
  while d1 <= n_minus_1
    invariant 1 <= d1 <= n_minus_1 + 1
    invariant count1 == |set d: nat | 1 <= d < d1 && n_minus_1 % d == 0|
  {
    if n_minus
// </vc-code>

