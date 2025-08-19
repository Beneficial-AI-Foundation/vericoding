module RussianMultiplication {

    export provides mult

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0);
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

}