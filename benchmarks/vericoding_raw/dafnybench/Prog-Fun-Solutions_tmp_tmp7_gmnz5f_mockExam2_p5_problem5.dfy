// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

// <vc-helpers>
// </vc-helpers>

method problem5(n:nat) returns (x: int)
ensures x == f(n)
// <vc-code>
{
  assume false;
}
// </vc-code>