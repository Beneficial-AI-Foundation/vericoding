

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
// </vc-spec>
// <vc-code>
{
  var rr:int := x;
  var qq:int := 0;
  while y <= rr
    invariant 0 <= rr
    invariant 0 <= qq
    invariant 0 < y
    invariant qq * y + rr == x
    decreases rr
  {
    rr := rr - y;
    qq := qq + 1;
  }
  r := rr;
  q := qq;
}
// </vc-code>

