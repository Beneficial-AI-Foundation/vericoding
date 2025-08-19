The method needs to satisfy:
- Input: `a >= 0` and `b > 0`
- Output: `a == b*c + r` and `0 <= r < b`

This is a classic division algorithm where we repeatedly subtract the divisor from the dividend until we can't subtract anymore.

//IMPL
method div_ent_it(a: int, b: int) returns (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

  requires a >= 0 && b > 0
  ensures a == b*c + r && 0 <= r < b
{
  c := 0;
  r := a;
  
  while r >= b
    invariant a == b*c + r
    invariant r >= 0
  {
    r := r - b;
    c := c + 1;
  }
}