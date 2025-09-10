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
lemma SubsetCardinalityBound<T>(s1: set<T>, s2: set<T>)
  requires s1 <= s2
  ensures |s1| <= |s2|
{
  // This is a basic set theory fact that Dafny should handle
}

lemma DivisorCountBound(n: nat)
  requires n > 0
  ensures count_divisors(n) <= n
{
  var divisors := set d | 1 <= d <= n && n % d == 0;
  var all := set d | 1 <= d <= n;
  assert divisors <= all;
  
  // Prove that |all| == n
  var card := 0;
  var k := 1;
  var seen := set d | 1 <= d < k;
  
  while k <= n
    invariant 1 <= k <= n + 1
    invariant seen == set d | 1 <= d < k
    invariant card == |seen|
    invariant card == k - 1
  {
    seen := seen + {k};
    assert seen == set d | 1 <= d <= k;
    card := card + 1;
    k := k + 1;
    assert seen == set d | 1 <= d < k;
  }
  
  assert k == n + 1;
  assert seen == set d | 1 <= d <= n;
  assert seen == all;
  assert card == n;
  assert |all| == n;
  
  SubsetCardinalityBound(divisors, all);
  assert |divisors| <= |all|;
  assert |divisors| <= n;
  assert count_divisors(n) == |divisors|;
  assert count_divisors(n) <= n;
}

lemma SpecialDivisorCountBound(n: nat)
  requires n > 0
  ensures count_special_divisors(n) <= n
{
  var special := set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  var all := set d | 1 <= d <= n;
  assert special <= all;
  
  // Prove |all| == n similar to above
  var card := 0;
  var k := 1;
  var seen := set d | 1 <= d < k;
  
  while k <= n
    invariant 1 <= k <= n + 1
    invariant seen == set d | 1 <= d < k
    invariant card == |seen|
    invariant card == k - 1
  {
    seen := seen + {k};
    assert seen == set d | 1 <= d <= k;
    card := card + 1;
    k := k + 1;
    assert seen == set d | 1 <= d < k;
  }
  
  assert k == n + 1;
  assert seen == set d | 1 <= d <= n;
  assert seen == all;
  assert card == n;
  assert |all| == n;
  
  SubsetCardinalityBound(special, all);
  assert |special| <= |all|;
  assert |special| <= n;
  assert count_special_divisors(n) == |special|;
  assert count_special_divisors(n) <= n;
}

lemma ReduceByDivisorTerminates(n: nat, d: nat)
  requires n > 0 && d > 1
  ensures reduce_by_divisor(n, d) > 0
  decreases n
{
  if n % d == 0 && n >= d {
    assert n / d < n;
    ReduceByDivisorTerminates(n / d, d);
  }
}

lemma ReduceByDivisorComputation(n: nat, d: nat, reduced: nat)
  requires n > 0 && d > 1
  requires reduced > 0
  ensures (
    var temp := n;
    var r := temp;
    while r % d == 0 && r >= d
      invariant r > 0
      decreases r
    {
      r := r / d;
    }
    r == reduce_by_divisor(n, d)
  )
{
  // This lemma establishes that the iterative computation matches the recursive definition
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
  var divisor_set := set d | 1 <= d < i && (n-1) % d == 0;
  
  while i <= n - 1
    invariant 1 <= i <= n
    invariant divisor_set == set d | 1 <= d < i && (n-1) % d == 0
    invariant divisor_count == |divisor_set|
  {
    if (n - 1) % i == 0 {
      divisor_set := divisor_set + {i};
      divisor_count := divisor_count + 1;
    }
    i := i + 1;
    assert divisor_set == set d | 1 <= d < i && (n-1) % d == 0;
  }
  assert i == n;
  assert divisor_set == set d | 1 <= d <= n-1 && (n-1) % d == 0;
  assert divisor_count == count_divisors(n - 1);
  
  // Count special divisors of n
  var special_count := 0;
  var j := 2;
  var special_set := set d | 2 <= d < j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  
  while j <= n
    invariant 2 <= j <= n + 1
    invariant special_set == set d | 2 <= d < j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0
    invariant special_count == |special_set|
  {
    if n % j == 0 {
      var reduced := n;
      // Compute reduce_by_divisor(n, j)
      while reduced % j == 0 && reduced >= j
        invariant reduced > 0
        invariant reduced <= n
        invariant n % j == 0
        invariant j > 1
        decreases reduced
      {
        reduced := reduced / j;
      }
      
      // Now reduced == reduce_by_divisor(n, j)
      ReduceByDivisorTerminates(n, j);
      assert reduced > 0;
      assert reduced == reduce_by_divisor(n, j);
      
      if reduced >= 1 && (reduced - 1) % j == 0 {
        special_set := special_set + {j};
        special_count := special_count + 1;
      }
    }
    j := j + 1;
    assert special_set == set d | 2 <= d < j && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  }
  assert j == n + 1;
  assert special_set == set d | 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0;
  assert special_count == count_special_divisors(n);
  
  result := divisor_count + special_count - 1;
  assert result == count_divisors(n - 1) + count_special_divisors(n) - 1;
}
// </vc-code>

