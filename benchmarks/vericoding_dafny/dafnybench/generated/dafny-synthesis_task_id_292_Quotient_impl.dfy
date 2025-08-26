method Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
// </vc-spec>
// <vc-code>
{
  result := a / b;
}
// </vc-code>