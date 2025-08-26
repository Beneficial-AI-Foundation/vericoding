method Carre(a: nat) returns (c: nat)
ensures c == a*a
// </vc-spec>
// <vc-code>
{
  c := a * a;
}
// </vc-code>