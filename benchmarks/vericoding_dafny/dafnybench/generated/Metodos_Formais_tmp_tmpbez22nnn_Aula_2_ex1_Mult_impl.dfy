method Mult(x:nat, y:nat) returns (r: nat)
ensures r == x * y
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == i * x
  {
    r := r + x;
    i := i + 1;
  }
}
// </vc-code>