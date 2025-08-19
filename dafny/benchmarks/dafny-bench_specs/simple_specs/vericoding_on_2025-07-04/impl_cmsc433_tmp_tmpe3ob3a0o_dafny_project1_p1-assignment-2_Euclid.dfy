//IMPL 

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers. If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator). Write requires and
// ensures clauses for the method header Euclid below. Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

/* code modified by LLM (iteration 4): Fixed gcd function preconditions to handle b = 0 case */
function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

/* code modified by LLM (iteration 4): Fixed IsGCD predicate to handle all valid cases */
predicate IsGCD(g: int, a: int, b: int)
  requires a > 0 && b >= 0
{
  g > 0 && a % g == 0 && (b == 0 || b % g == 0) &&
  forall d :: d > 0 && a % d == 0 && (b == 0 || b % d == 0) ==> d <= g
}

/* code modified by LLM (iteration 4): Fixed lemma preconditions and proof */
lemma GCDProperties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures IsGCD(gcd(a, b), a, b)
  decreases b
{
  if b == 0 {
    // Base case: gcd(a, 0) = a, and a divides a
    assert gcd(a, 0) == a;
    assert a % a == 0;
    // Prove that a is the greatest divisor of a
    forall d | d > 0 && a % d == 0
      ensures d <= a
    {
      // Any divisor of a must be at most a
    }
  } else {
    GCDProperties(b, a % b);
    // The gcd is preserved through the Euclidean step
    assert gcd(a, b) == gcd(b, a % b);
    
    // Prove that common divisors are preserved
    forall d | d > 0
      ensures (a % d == 0 && b % d == 0) <==> (b % d == 0 && (a % b) % d == 0)
    {
      if a % d == 0 && b % d == 0 {
        // If d divides both a and b, then d divides a % b
        assert (a % b) % d == 0;
      }
      if b % d == 0 && (a % b) % d == 0 {
        // If d divides b and a % b, then d divides a
        assert a % d == 0;
      }
    }
  }
}

/* code modified by LLM (iteration 4): Added helper lemma for modulo properties */
lemma ModuloLemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % b < b
  ensures a % b >= 0
{
}

method Euclid (m : int, n : int) returns (gcd_result : int)
  requires m > 1 && n > 1 && m >= n
  ensures gcd_result > 0 && gcd_result <= n && gcd_result <= m && m % gcd_result == 0 && n % gcd_result == 0
  ensures IsGCD(gcd_result, m, n)
{
  var a := m;
  var b := n;
  
  /* code modified by LLM (iteration 4): Enhanced loop invariant with proper GCD preservation */
  while b != 0
    invariant a > 0 && b >= 0
    invariant gcd(a, b) == gcd(m, n)
    invariant b == 0 ==> (a == gcd(m, n) && IsGCD(a, m, n))
    decreases b
  {
    /* code modified by LLM (iteration 4): Added assertion to help with verification */
    assert b > 0;
    ModuloLemma(a, b);
    var temp := a % b;
    /* code modified by LLM (iteration 4): Added assertion about GCD preservation */
    assert gcd(a, b) == gcd(b, temp);
    a := b;
    b := temp;
  }
  
  gcd_result := a;
  
  /* code modified by LLM (iteration 4): Enhanced postcondition proof */
  assert b == 0;
  assert gcd_result == a;
  assert gcd(a, 0) == a;
  assert gcd_result == gcd(m, n);
  
  GCDProperties(m, n);
  assert IsGCD(gcd(m, n), m, n);
  assert IsGCD(gcd_result, m, n);
  
  /* code modified by LLM (iteration 4): Explicit proof of basic postconditions */
  assert gcd_result > 0; // From IsGCD property
  assert m % gcd_result == 0; // From IsGCD property
  assert n % gcd_result == 0; // From IsGCD property
  
  // Prove gcd_result <= n and gcd_result <= m
  assert gcd_result <= m && gcd_result <= n by {
    // Since gcd_result divides both m and n, and both are positive,
    // gcd_result cannot exceed either of them
    assert m % gcd_result == 0 && m > 0;
    assert n % gcd_result == 0 && n > 0;
  }
}