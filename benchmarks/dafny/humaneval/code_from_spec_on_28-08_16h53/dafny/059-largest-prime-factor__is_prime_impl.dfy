function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma PrimeFactorExists(n: int)
  requires n >= 2
  ensures exists p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0
{
  if n == 2 {
    assert is_prime_pred(2);
    assert n % 2 == 0;
  } else {
    var smallest := SmallestFactor(n);
    assert 2 <= smallest <= n;
    assert is_prime_pred(smallest);
    assert n % smallest == 0;
  }
}

function SmallestFactor(n: int): int
  requires n >= 2
  ensures 2 <= SmallestFactor(n) <= n
  ensures n % SmallestFactor(n) == 0
  ensures is_prime_pred(SmallestFactor(n))
{
  if n == 2 then 2
  else if n % 2 == 0 then 2
  else SmallestOddFactor(n, 3)
}

function SmallestOddFactor(n: int, k: int): int
  requires n >= 3 && n % 2 != 0
  requires k >= 3 && k % 2 == 1
  ensures 2 <= SmallestOddFactor(n, k) <= n
  ensures n % SmallestOddFactor(n, k) == 0
  ensures is_prime_pred(SmallestOddFactor(n, k))
{
  if k * k > n then n
  else if n % k == 0 then k
  else SmallestOddFactor(n, k + 2)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_prime(k: int) returns (result: bool)
Check if condition holds. Requires: the result is at least the specified value. Ensures: the condition holds for all values; there exists a value satisfying the condition.
*/
// </vc-description>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  requires k >= 2
  ensures result == is_prime_pred(k)
// </vc-spec>
// <vc-code>
method is_prime(k: int) returns (result: bool)
  requires k >= 2
  ensures result == is_prime_pred(k)
{
  if k == 2 {
    result := true;
    return;
  }
  
  if k % 2 == 0 {
    result := false;
    return;
  }
  
  var i := 3;
  while i * i <= k
    invariant i >= 3 && i % 2 == 1
    invariant forall j :: 2 <= j < i ==> k % j != 0
    decreases k - i * i
  {
    if k % i == 0 {
      result := false;
      return;
    }
    i := i + 2;
  }
  
  result := true;
}
// </vc-code>

method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
{
  assume{:axiom} false;
}