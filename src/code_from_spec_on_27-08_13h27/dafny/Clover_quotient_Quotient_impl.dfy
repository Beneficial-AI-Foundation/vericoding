// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
// </vc-spec>
// </vc-spec>

// <vc-code>
method QuotientImpl(x: nat, y: nat) returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  q := 0;
  r := x;
  while r >= y
    decreases r
    invariant q * y + r == x && 0 <= r
  {
    q := q + 1;
    r := r - y;
  }
}
// </vc-code>
