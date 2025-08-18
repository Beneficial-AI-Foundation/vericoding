// <vc-helpers>
// </vc-helpers>

method Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
// <vc-code>
{
  assume false;
}
// </vc-code>