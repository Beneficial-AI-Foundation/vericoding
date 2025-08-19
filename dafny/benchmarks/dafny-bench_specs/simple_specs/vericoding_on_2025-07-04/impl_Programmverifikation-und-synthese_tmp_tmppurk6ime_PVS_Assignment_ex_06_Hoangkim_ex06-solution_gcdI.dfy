//ATOM
ghost function gcd'(x:int,y:int):int
 requires x > 0 && y > 0
{
 if x==y then x
 else if x > y then gcd'(x-y,y)
 else gcd'(y,x)
}

//IMPL gcdI
/* code modified by LLM (iteration 3): added helper lemma to prove gcd symmetry and subtraction property */
lemma gcdSymmetryAndSubtraction(x: int, y: int)
  requires x > 0 && y > 0 && x < y
  ensures gcd'(x, y) == gcd'(x, y - x)
{
  assert gcd'(x, y) == gcd'(y, x);
  assert gcd'(y, x) == gcd'(y - x, x);
  assert gcd'(y - x, x) == gcd'(x, y - x);
}

method gcdI(m:int, n:int) returns (d:int)
 requires m > 0 && n > 0
 ensures  d == gcd'(m,n) 
{
  /* code modified by LLM (iteration 3): implemented iterative GCD algorithm with helper lemma */
  var x := m;
  var y := n;
  
  while x != y
    invariant x > 0 && y > 0
    invariant gcd'(x, y) == gcd'(m, n)
    decreases x + y
  {
    if x > y {
      /* code modified by LLM (iteration 3): assertion to help prove invariant preservation when x > y */
      assert gcd'(x, y) == gcd'(x - y, y);
      x := x - y;
    } else {
      /* code modified by LLM (iteration 3): use helper lemma to prove invariant preservation when x < y */
      assert x < y;
      gcdSymmetryAndSubtraction(x, y);
      y := y - x;
    }
  }
  
  d := x;
}