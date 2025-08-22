//IMPL Euclid

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers. If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator). Write requires and
// ensures clauses for the method header Euclid below. Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

/* code modified by LLM (iteration 4): Added helper function to define gcd mathematically with proper termination */
function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd_func(b, a % b)
}

/* code modified by LLM (iteration 4): Added comprehensive lemma to prove gcd properties */
lemma gcd_properties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd_func(a, b) == 0
  ensures b % gcd_func(a, b) == 0
  ensures gcd_func(a, b) > 0
  decreases b
{
  if b == 0 {
    // base case: gcd_func(a, 0) == a
    assert gcd_func(a, b) == a;
  } else {
    gcd_properties(b, a % b);
    assert gcd_func(a, b) == gcd_func(b, a % b);
  }
}

/* code modified by LLM (iteration 4): Added lemma to prove gcd invariant preservation */
lemma gcd_invariant(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd_func(a, b) == gcd_func(b, a % b)
{
  // This follows directly from the definition of gcd_func
}

/* code modified by LLM (iteration 4): Added lemma to prove modulo properties */
lemma modulo_property(a: int, b: int)
  requires a > 0 && b > 0
  ensures 0 <= a % b < b
{
}

method Euclid (m : int, n : int) returns (gcd : int)
  requires m > 0 && n > 0 && m >= n
  ensures gcd > 0
  ensures m % gcd == 0 && n % gcd == 0
  ensures gcd == gcd_func(m, n)
{
  /* code modified by LLM (iteration 4): Fixed implementation with proper initialization and invariants */
  var a := m;
  var b := n;
  
  while b != 0
    invariant a > 0 && b >= 0
    invariant gcd_func(a, b) == gcd_func(m, n)
    decreases b
  {
    /* code modified by LLM (iteration 4): Added proper loop body with lemma calls */
    gcd_invariant(a, b);
    modulo_property(a, b);
    
    var temp := a % b;
    a := b;
    b := temp;
  }
  
  gcd := a;
  
  /* code modified by LLM (iteration 4): Added proof support for postconditions */
  assert b == 0;
  assert gcd_func(a, 0) == a;
  assert gcd == a;
  assert gcd == gcd_func(a, b);
  assert gcd == gcd_func(m, n);
  
  gcd_properties(m, n);
}