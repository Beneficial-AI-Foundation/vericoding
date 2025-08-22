// ATOM 

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
{
  if x==y then x
  else if x > y then gcd'(x-y,y)
  else gcd'(y,x)
}

// IMPL 

/* code modified by LLM (iteration 4): added helper lemma to prove gcd properties */
lemma gcdProperties(x: int, y: int)
  requires x > 0 && y > 0
  ensures x > y ==> gcd'(x, y) == gcd'(x - y, y)
  ensures y > x ==> gcd'(x, y) == gcd'(y, x)
{
  // The lemma body is empty because these follow directly from the definition of gcd'
}

method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd'(m,n) 
{
  var x := m;
  var y := n;
  
  while x != y
    invariant x > 0 && y > 0
    invariant gcd'(x,y) == gcd'(m,n)
    /* code modified by LLM (iteration 4): kept the correct decreases clause */
    decreases x + y
  {
    if x > y {
      /* code modified by LLM (iteration 4): use helper lemma to establish gcd property */
      gcdProperties(x, y);
      x := x - y;
    } else {
      /* code modified by LLM (iteration 4): use helper lemma to establish gcd property */
      gcdProperties(x, y);
      y := y - x;
    }
  }
  
  d := x;
}