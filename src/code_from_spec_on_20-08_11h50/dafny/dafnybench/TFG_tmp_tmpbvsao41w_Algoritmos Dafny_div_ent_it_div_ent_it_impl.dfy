method div_ent_it(a: int, b: int) returns (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
// </vc-spec>
// <vc-code>
{
  c := 0;
  r := a;
  
  while r >= b
    invariant a == b*c + r && r >= 0
    decreases r
  {
    r := r - b;
    c := c + 1;
  }
}
// </vc-code>