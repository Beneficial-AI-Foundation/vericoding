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
  
  // The cardinality of all is exactly n
  var card := 0;
  var k := 1;
  while k <= n
    invariant 1 <= k <= n + 1
    invariant card == k - 1
    invariant card == |set d | 1 <= d < k|
  {
    card := card + 1;
    k := k + 1;
  }
  assert card == n;
  assert |all| == n;
  assert |divisors| <= |all|;
}

lemma SpecialDivisorCountBound(n: nat)
  requires n > 0
  ensures count_special_divisors(n) <= n
{
  var special := set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  var all := set d | 1 <= d <= n;
  assert special <= all;
  
  // Similar reasoning - all has cardinality n
  assert |all| == n;
  assert |special| <= |all|;
}

lemma ReduceByDivisorCorrectness(n: nat, d: nat, result: nat)
  requires n > 0 && d > 1
  requires result > 0
  ensures (n % d != 0 || n < d) && result == n ==> reduce_by_divisor(n, d) == result
  ensures n % d == 0 && n >= d && result == n / d ==> 
    reduce_by_divisor(n, d) == reduce_by_divisor(result, d)
{
  // This follows directly from the definition
}

lemma ReduceByDivisorComputation(n: nat, d: nat, reduced: nat)
  requires n > 0 && d > 1 && reduced > 0
  requires reduced % d != 0 || reduced < d
  requires forall k: nat :: k > 0 && k % d == 0 && k >= d && reduced == k / d ==> false
  ensures reduce_by_divisor(n, d) == reduced ==> 
    exists steps: nat :: reduced == n / (if n % d == 0 then d else 1)
{
  // Helper to reason about the computation
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
  
  DivisorCountBound(n - 1);
  SpecialDivisorCountBound(n);
  
  // Count divisors of n-1
  var divisor_count := 0;
  var i := 1;
  while i <= n - 1
    invariant 1 <= i <= n
    invariant divisor_count == |set d | 1 <= d < i && (n-1) % d == 0|
  {
    if (n - 1) % i == 0 {
      divisor_count := divisor_count + 1;
      // Update the set comprehension
      assert i in set d | 1 <= d <= i && (n-1) % d == 0;
      assert divisor_count == |set d | 1 <= d <= i && (n-1) % d == 0|;
    }
    i := i + 1;
  }
  assert divisor_count == count_divisors(n - 1);
  
  // Count special divisors of n
  var special_count := 0;
  var j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant special_count == |set d | 2 <= d < j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|
  {
    if n % j == 0 {
      var reduced := n;
      // Compute reduce_by_divisor(n, j)
      while reduced % j == 0 && reduced >= j
        invariant reduced > 0
        invariant reduced <= n
        invariant n % j == 0
        decreases reduced
      {
        reduced := reduced / j;
      }
      
      // At this point, reduced == reduce_by_divisor(n, j)
      if reduced >= 1 && (reduced - 1) % j == 0 {
        special_count := special_count + 1;
        assert j in set d | 2 <= d <= j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
        assert special_count == |set d | 2 <= d <= j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0|;
      }
    }
    j := j + 1;
  }
  assert special_count == count_special_divisors(n);
  
  result := divisor_count + special_count - 1;
  assert result == count_divisors(n - 1) + count_special_divisors(n) - 1;
}
// </vc-code>

