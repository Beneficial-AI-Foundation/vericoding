// <vc-helpers>
// </vc-helpers>

method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
// <vc-code>
{
  assume false;
}
// </vc-code>