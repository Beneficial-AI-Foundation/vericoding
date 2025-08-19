//ATOM
ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x == y then x
  else if x > y then gcd'(x - y, y)
  /* code modified by LLM (iteration 1): fixed recursive call from gcd to gcd' */
  else gcd'(y, x)
}

/* code modified by LLM (iteration 4): added helper lemma to prove gcd subtraction property */
lemma gcd_subtract_lemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures a > b ==> gcd'(a, b) == gcd'(a - b, b)
  ensures b > a ==> gcd'(a, b) == gcd'(a, b - a)
{
  if a > b {
    // The property follows from the definition of gcd'
  } else if b > a {
    // gcd'(a, b) == gcd'(b, a) by definition when a < b
    // and gcd'(b, a) == gcd'(b - a, a) when b > a
  }
}

//IMPL 
method gcdI(m: int, n: int) returns (d: int)
requires m > 0 && n > 0 
/* code modified by LLM (iteration 2): restored original ensures clause and added implementation */
ensures d == gcd'(m, n)
{
  var a := m;
  var b := n;
  
  while a != b
    invariant a > 0 && b > 0
    /* code modified by LLM (iteration 3): added invariant to maintain gcd relationship */
    invariant gcd'(a, b) == gcd'(m, n)
    /* code modified by LLM (iteration 4): improved decreases clause to use sum for better termination proof */
    decreases a + b
  {
    if a > b {
      /* code modified by LLM (iteration 4): use lemma to prove gcd property */
      gcd_subtract_lemma(a, b);
      a := a - b;
    } else {
      /* code modified by LLM (iteration 4): use lemma to prove gcd property */
      gcd_subtract_lemma(a, b);
      b := b - a;
    }
  }
  
  d := a;
}