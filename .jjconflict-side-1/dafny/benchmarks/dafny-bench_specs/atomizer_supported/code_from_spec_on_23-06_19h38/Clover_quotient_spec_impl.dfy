//IMPL 
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while r >= y
    invariant q * y + r == x
    invariant r >= 0
    invariant q >= 0
  {
    r := r - y;
    q := q + 1;
  }
}