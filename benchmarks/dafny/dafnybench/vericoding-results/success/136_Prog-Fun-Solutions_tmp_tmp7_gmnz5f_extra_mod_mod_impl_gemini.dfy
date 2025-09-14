// <vc-preamble>
ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
  var i := n;
  var res: nat := 0;
  var factor: nat := 1;
  while i > 0
    invariant f(n) == res + factor * f(i)
    decreases i
  {
    if i % 2 == 0 {
      res := res + factor;
    }
    factor := 2 * factor;
    i := i / 2;
  }
  a := res + factor;
}
// </vc-code>
