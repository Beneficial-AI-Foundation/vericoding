// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
// </vc-spec>
// <vc-code>
{
  var a := x1;
  var b := x2;
  
  while b != 0
    invariant a > 0 && b >= 0
  {
    var temp := a % b;
    a := b;
    b := temp;
  }
}
// </vc-code>