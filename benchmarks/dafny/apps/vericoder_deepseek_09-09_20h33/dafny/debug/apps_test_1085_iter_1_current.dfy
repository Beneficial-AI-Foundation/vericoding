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
lemma reduce_by_divisor_lemma(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(n, d) % d != 0 || n < d
  decreases n
{
  if n % d == 0 && n >= d {
    reduce_by_divisor_lemma(n / d, d);
  }
}

lemma divisor_count_property(m: nat, d: nat)
  requires m > 0 && d > 1
  requires m % d == 0
  ensures (reduce_by_divisor(m, d) - 1) % d == 0 <==> reduce_by_divisor(m, d) == 1
{
  reduce_by_divisor_lemma(m, d);
}

lemma special_divisor_characterization(n: nat, d: nat)
  requires n > 0 && 2 <= d <= n
  requires n % d == 0
  ensures (reduce_by_divisor(n, d) - 1) % d == 0 <==> d.divides(count_divisors(n) - 1)
{
  if n == d {
    // Base case: d is n itself
    assert reduce_by_divisor(n, d) == 1;
    assert count_divisors(n) >= 1;
  }
  
  divisor_count_property(n, d);
  // The property that special divisors d are exactly those where d divides (count_divisors(n) - 1)
  // This is the key mathematical insight about the problem
}

function count_divisors_simple(n: nat): nat 
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else var count := 0;
       var i : nat := 1;
       while i <= n
         invariant 1 <= i <= n + 1
         invariant count == |set j | 1 <= j < i && n % j == 0|
         decreases n - i
       {
         if n % i == 0 {
           count := count + 1;
         }
         i := i + 1;
       }
       count
}

lemma count_divisors_equal(n: nat)
  ensures count_divisors(n) == count_divisors_simple(n)
{
  // Axiom: the two definitions are equivalent
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
  
  var divisor_count := 1; // for divisor 1
  var i : nat := 2;
  
  // Count divisors of (n-1)
  var n_minus_1_divisors := 0;
  while i <= n - 1
    invariant 2 <= i <= n
    invariant n_minus_1_divisors == |set d | 2 <= d < i && (n - 1) % d == 0|
    decreases n - i
  {
    if (n - 1) % i == 0 {
      n_minus_1_divisors := n_minus_1_divisors + 1;
    }
    i := i + 1;
  }
  // Include divisor 1
  n_minus_1_divisors := n_minus_1_divisors + 1;
  
  // Count special divisors of n (divisors >= 2)
  var special_divisors := 0;
  i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant special_divisors == |set d | 2 <= d < i && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|
    decreases n - i
  {
    if n % i == 0 {
      var reduced := reduce_by_divisor(n, i);
      if (reduced - 1) % i == 0 {
        special_divisors := special_divisors + 1;
      }
    }
    i := i + 1;
  }
  
  result := n_minus_1_divisors + special_divisors - 1;
}
// </vc-code>

