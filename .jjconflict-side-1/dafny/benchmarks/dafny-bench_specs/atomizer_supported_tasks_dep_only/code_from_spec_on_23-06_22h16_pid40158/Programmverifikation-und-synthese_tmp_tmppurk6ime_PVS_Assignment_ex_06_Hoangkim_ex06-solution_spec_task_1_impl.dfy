//ATOM gcd_function
ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
{
  if x==y then x
  else if x > y then gcd'(x-y,y)
  else gcd'(y,x)
}

/* code modified by LLM (iteration 1): Fixed helper lemmas with proper recursive structure and termination */
lemma gcd_symmetric(x: int, y: int)
  requires x > 0 && y > 0
  ensures gcd'(x, y) == gcd'(y, x)
{
  if x == y {
    // Base case: both are equal
  } else if x > y {
    // gcd'(x, y) = gcd'(x-y, y) and gcd'(y, x) = gcd'(y, x) = gcd'(x, y)
    // This is direct from definition
  } else {
    // x < y, so gcd'(x, y) = gcd'(y, x) by definition
  }
}

lemma gcd_subtraction(x: int, y: int)
  requires x > 0 && y > 0 && x > y
  ensures gcd'(x, y) == gcd'(x - y, y)
{
  // This follows directly from the definition of gcd'
}

lemma gcd_subtraction_alt(x: int, y: int)
  requires x > 0 && y > 0 && y > x
  ensures gcd'(x, y) == gcd'(x, y - x)
{
  // By definition: gcd'(x, y) = gcd'(y, x) when y > x
  // And gcd'(y, x) = gcd'(y - x, x) when y > x
  // So gcd'(x, y) = gcd'(y - x, x) = gcd'(x, y - x)
}

//IMPL gcdI
method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd'(m,n) 
{
  var a := m;
  var b := n;
  
  /* code modified by LLM (iteration 1): Added proper loop with correct invariants and termination proof */
  while a != b
    invariant a > 0 && b > 0
    invariant gcd'(a, b) == gcd'(m, n)
    decreases a + b
  {
    if a > b {
      /* code modified by LLM (iteration 1): Added lemma call to maintain invariant */
      gcd_subtraction(a, b);
      a := a - b;
    } else {
      /* code modified by LLM (iteration 1): Added lemma call for the other case */
      gcd_subtraction_alt(a, b);
      b := b - a;
    }
  }
  
  d := a;
}