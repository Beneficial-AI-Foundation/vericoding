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
    var k := 1;
    var cnt_div := 0;
    while k <= n - 1
      decreases n - 1 - k
    {
      if (n - 1) % k == 0 {
        cnt_div := cnt_div + 1;
      }
      k := k + 1;
    }
    var q := 2;
    var cnt_special := 0;
    while q <= n
      decreases n - q
    {
      if n % q == 0 {
        var m := n;
        while m % q == 0 && m >= q
          decreases m
        {
          m := m / q;
        }
        if (m - 1) % q == 0 {
          cnt_special := cnt_special + 1;
        }
      }
      q := q + 1;
    }
    result := cnt_div + cnt_special - 1;
  }
}
// </vc-code>

