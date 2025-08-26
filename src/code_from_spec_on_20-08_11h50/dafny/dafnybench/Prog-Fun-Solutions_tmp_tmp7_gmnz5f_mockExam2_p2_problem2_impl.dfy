method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
// </vc-spec>
// <vc-code>
{
  r := q - 3;
  s := p - 2*q + 6;
}
// </vc-code>