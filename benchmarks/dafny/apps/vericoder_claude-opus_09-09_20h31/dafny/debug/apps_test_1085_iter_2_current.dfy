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
lemma DivisorCountBound(n: nat)
  requires n > 0
  ensures count_divisors(n) <= n
{
  var divisors := set d | 1 <= d <= n && n % d == 0;
  var all := set d | 1 <= d <= n;
  assert divisors <= all;
  
  // Prove |all| == n by showing bijection with 1..n
  var mapping := map i: int | 1 <= i <= n :: i;
  assert forall i :: 1 <= i <= n ==> i in all;
  assert forall d :: d in all ==> 1 <= d <= n;
  
  // Since divisors is a subset of all, and all has at most n elements
  assert |divisors| <= n;
}

lemma SpecialDivisorCountBound(n: nat)
  requires n > 0
  ensures count_special_divisors(n) <= n
{
  var special := set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  var all := set d | 1 <= d <= n;
  assert special <= all;
  
  // Similar reasoning as above
  assert |special| <= n;
}

lemma ReduceByDivisorProperties(n: nat, d: nat, current: nat)
  requires n > 0 && d > 1 && current > 0
  requires n % d == 0 && current == n
  ensures reduce_by_divisor(n, d) == reduce_by_divisor(current, d)
{
  // This follows from the definition
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
  
  // Count divisors of n-1
  var divisor_count := 0;
  var i := 1;
  while i <= n - 1
    invariant 1 <= i <= n
    invariant divisor_count == |set d | 1 <= d < i && (n-1) % d == 0|
  {
    if (n - 1) % i == 0 {
      divisor_count := divisor_count + 1;
    }
    i := i + 1;
  }
  
  // Count special divisors of n
  var special_count := 0;
  var j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant special_count == |set d | 2 <= d < j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|
  {
    if n % j == 0 {
      var reduced := n;
      var original := n;
      while reduced % j == 0 && reduced >= j
        invariant reduced > 0
        invariant n % j == 0
        invariant original == n
        invariant reduced % j == 0 ==> reduced >= j
        decreases reduced
      {
        reduced := reduced / j;
      }
      
      // Now check if reduced satisfies the condition
      assert reduced == reduce_by_divisor(n, j);
      if reduced >= 1 && (reduced - 1) % j == 0 {
        special_count := special_count + 1;
      }
    }
    j := j + 1;
  }
  
  result := divisor_count + special_count - 1;
}
// </vc-code>

