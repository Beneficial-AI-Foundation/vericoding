// <vc-preamble>
ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
  a := 0;
  var i := n;
  var p: nat := 1;
  while i > 0
    invariant a + p * f2(i) == f2(n)
    decreases i
  {
    a := a + p * (i % 4);
    p := p * 5;
    i := i / 3;
  }
}
// </vc-code>
