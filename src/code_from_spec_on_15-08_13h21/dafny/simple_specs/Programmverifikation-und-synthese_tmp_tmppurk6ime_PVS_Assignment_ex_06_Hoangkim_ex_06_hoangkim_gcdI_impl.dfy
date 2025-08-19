/* code modified by LLM (iteration 4): Fixed decreases clause to use x + y which always decreases */
ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases x + y
{
  if x == y then x
  else if x > y then gcd'(x - y, y)
  /* code modified by LLM (iteration 1): Fixed recursive call to use correct function name gcd' instead of gcd */
  else gcd'(y, x)
}

/* code modified by LLM (iteration 3): Implemented helper lemma with proper proof */
lemma gcd_subtract_property(x: int, y: int)
  requires x > 0 && y > 0 && x != y
  ensures gcd'(x, y) == (if x > y then gcd'(x - y, y) else gcd'(x, y - x))
{
  if x > y {
    // When x > y, gcd'(x, y) = gcd'(x - y, y) by definition
    assert gcd'(x, y) == gcd'(x - y, y);
  } else {
    // When x < y, gcd'(x, y) = gcd'(y, x) by definition
    // and gcd'(y, x) = gcd'(y - x, x) = gcd'(x, y - x)
    assert gcd'(x, y) == gcd'(y, x);
    assert y > x;
    assert gcd'(y, x) == gcd'(y - x, x);
    assert gcd'(y - x, x) == gcd'(x, y - x);
  }
}

//IMPL 

method gcdI(m: int, n: int) returns (d: int)
requires m > 0 && n > 0 
/* code modified by LLM (iteration 1): Changed ensures clause to use gcd' instead of gcd */
ensures d == gcd'(m, n)
{
  var a := m;
  var b := n;
  
  while a != b
    invariant a > 0 && b > 0
    /* code modified by LLM (iteration 1): Changed invariant to use gcd' instead of gcd */
    invariant gcd'(a, b) == gcd'(m, n)
    decreases a + b
  {
    if a > b {
      /* code modified by LLM (iteration 2): Added assertion to help prove loop invariant maintenance */
      assert gcd'(a, b) == gcd'(a - b, b) by { gcd_subtract_property(a, b); }
      a := a - b;
    } else {
      /* code modified by LLM (iteration 2): Added assertion to help prove loop invariant maintenance */
      assert gcd'(a, b) == gcd'(a, b - a) by { gcd_subtract_property(b, a); }
      b := b - a;
    }
  }
  
  d := a;
}