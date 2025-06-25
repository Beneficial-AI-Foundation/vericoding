//ATOM
// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL 
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    /* code modified by LLM (iteration 1): Fixed the recursive call to use x and n/2, then square the result */
    powerEvenLemma(x, n);
    var half := powerOpt(x, n / 2);
    p := half * half;
  } else {
    var rest := powerOpt(x, n - 1);
    p := x * rest;
  }
}

/* code modified by LLM (iteration 1): Simplified lemma to prove the correct mathematical relationship */
lemma powerEvenLemma(x: real, n: nat)
  requires n % 2 == 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
  decreases n
{
  if n == 0 {
    // Base case: power(x, 0) = 1.0 = 1.0 * 1.0
    assert power(x, 0) == 1.0;
    assert power(x, 0) * power(x, 0) == 1.0;
  } else {
    // n >= 2 and even
    assert n >= 2;
    assert n % 2 == 0;
    
    /* code modified by LLM (iteration 1): Use induction to prove the relationship */
    // We need to show: power(x, n) == power(x, n/2) * power(x, n/2)
    // We'll use the fact that we can split the exponent
    powerSplitLemma(x, n / 2, n / 2);
    
    // Since n is even, n = (n/2) + (n/2)
    assert n == n / 2 + n / 2;
  }
}

/* code modified by LLM (iteration 1): Added helper lemma to prove power splitting property */
lemma powerSplitLemma(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
  decreases a
{
  if a == 0 {
    assert power(x, 0 + b) == power(x, b);
    assert power(x, 0) * power(x, b) == 1.0 * power(x, b) == power(x, b);
  } else {
    powerSplitLemma(x, a - 1, b);
    calc {
      power(x, a + b);
      == x * power(x, (a - 1) + b);
      == x * (power(x, a - 1) * power(x, b));
      == (x * power(x, a - 1)) * power(x, b);
      == power(x, a) * power(x, b);
    }
  }
}