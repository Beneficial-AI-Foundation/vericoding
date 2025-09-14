ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
  a := 0;
  var m: nat := n;
  var k: nat := 1;
  while m != 0
    invariant a + k * f2(m) == f2(n)
    decreases m
  {
    a := a + k * (m % 4);
    k := k * 5;
    m := m / 3;
  }
}
// </vc-code>

