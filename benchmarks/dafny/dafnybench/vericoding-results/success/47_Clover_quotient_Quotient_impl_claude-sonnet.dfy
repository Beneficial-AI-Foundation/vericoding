

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
// </vc-spec>
// <vc-code>
{
  q := 0;
  r := x;
  while r >= y
    invariant q * y + r == x
    invariant r >= 0
    invariant q >= 0
    decreases r
  {
    q := q + 1;
    r := r - y;
  }
}
// </vc-code>

