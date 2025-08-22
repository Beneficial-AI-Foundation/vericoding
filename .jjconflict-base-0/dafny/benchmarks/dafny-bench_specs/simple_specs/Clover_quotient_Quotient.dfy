// SPEC
method Quotient(x: nat, y:nat) returns (r:int, q:int)
 requires y != 0
 ensures q * y + r == x && 0 <= r < y && 0 <= q
{
}
