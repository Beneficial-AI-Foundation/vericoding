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
  } else {
    var div_count: nat := 0;
    for d: nat := 1 to n - 1
      invariant 1 <= d <= n
      invariant div_count == |set x | 1 <= x <= d - 1 && (n - 1) % x == 0|
    {
      if (n - 1) % d == 0 {
        div_count := div_count + 1;
      }
    }
    var special_count: nat := 0;
    for d: nat := 2 to n
      invariant 2 <= d <= n + 1
      invariant special_count == |set x | 2 <= x <= d - 1 && n % x == 0 && compute_reduced(n, x) - 1 % x == 0|
    {
      if n % d == 0 {
        var reduced: nat := compute_reduced(n, d);
        if (reduced - 1) % d == 0 {
          special_count := special_count + 1;
        }
      }
    }
    result := div_count + special_count - 1;
  }
}

method compute_reduced(nn: nat, dd: nat) returns (res: nat)
  requires nn > 0 && dd > 1
  ensures res == old(reduce_by_divisor(nn, dd))
{
  var current := nn;
  while current % dd == 0 && current >= dd
    invariant current > 0
    decreases current
  {
    current := current / dd;
  }
  res := current;
}
// </vc-code>

