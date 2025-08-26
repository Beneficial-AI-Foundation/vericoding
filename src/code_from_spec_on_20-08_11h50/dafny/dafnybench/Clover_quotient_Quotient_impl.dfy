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
    invariant 0 <= r
    invariant 0 <= q
    decreases r
  {
    q := q + 1;
    r := r - y;
  }
}
// </vc-code>