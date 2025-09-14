

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
// </vc-spec>
// <vc-code>
{
  r := x;
  q := 0;
  while r >= y
    invariant r + q * y == x && 0 <= r && 0 <= q
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
  return r, q;
}
// </vc-code>

