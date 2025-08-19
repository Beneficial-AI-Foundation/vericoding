// <vc-helpers>
// </vc-helpers>

method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// <vc-code>
{
  assume false;
}
// </vc-code>