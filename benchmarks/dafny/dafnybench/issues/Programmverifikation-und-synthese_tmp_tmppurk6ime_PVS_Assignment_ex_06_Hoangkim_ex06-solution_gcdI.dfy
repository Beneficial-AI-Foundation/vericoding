// <vc-preamble>
ghost function gcd(x:int,y:int):int
  requires x > 0 && y > 0 
{
  if x==y then x
  else if x > y then gcd(x-y,y)
  else gcd(x,y-x)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd(m,n)
// </vc-spec>
// <vc-code>
{
  var x,y := m,n;
        d := 1;
  while x != y
    decreases             x+y
    invariant             x > 0 && y > 0
    invariant             gcd(x,y) == gcd(m,n)   
   { if x > y { x := x-y; } else { y := y-x; }
   }
  d := x;
}
// </vc-code>

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
  decreases x+y,y        // x+y decreases or x+y remains unchanged while y decreases
{
  if x==y then x
  else if x > y then gcd'(x-y,y)
  else gcd'(y,x)
}